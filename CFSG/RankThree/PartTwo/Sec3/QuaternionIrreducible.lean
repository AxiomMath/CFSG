module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartTwo.Sec3.ThreeSpaceTransvections

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Module CFSG.RankThree.Classical

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

@[expose] def commutatorSpace (H : Subgroup (V ≃ₗ[ZMod 3] V)) : Submodule (ZMod 3) V :=
  Submodule.span (ZMod 3) {y | ∃ h ∈ H, ∃ v, h v - v = y}

theorem zmod3_neg_sub_self (y : V) : -y - y = y := by
  rw [← sub_eq_zero, show -y - y - y = -((3 : ℕ) • y) by abel, zmod3_three_smul, neg_zero]

theorem finrank_span_pair {v w : V} (h : LinearIndependent (ZMod 3) ![v, w]) :
    finrank (ZMod 3) (Submodule.span (ZMod 3) {v, w}) = 2 := by
  have hset : Set.range ![v, w] = ({v, w} : Set V) := by
    ext x
    simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
  have := finrank_span_eq_card h
  rw [hset] at this
  rw [this, Fintype.card_fin]

theorem linearIndependent_pair_of_apply_apply_eq_neg {h : V ≃ₗ[ZMod 3] V} {w : V}
    (hw : w ≠ 0) (hh : h (h w) = -w) : LinearIndependent (ZMod 3) ![w, h w] :=
  LinearIndependent.pair_iff.mpr fun s t hst => by
    have h2 : s • h w - t • w = 0 := by
      have := congrArg h hst
      rwa [map_add, map_smul, map_smul, hh, map_zero, smul_neg, ← sub_eq_add_neg] at this
    have h3 : (s * s + t * t) • w = 0 := by
      have : (s * s + t * t) • w = s • (s • w + t • h w) - t • (s • h w - t • w) := by module
      rw [this, hst, h2, smul_zero, smul_zero, sub_zero]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact (by decide : ∀ s t : ZMod 3, s * s + t * t = 0 → s = 0 ∧ t = 0) s t h4
    · exact absurd h4 hw

theorem isTransvectionWith_sq_mul_conj {z g : V ≃ₗ[ZMod 3] V} {u : V} {φ : Dual (ZMod 3) V}
    (hz : ∀ y, z y = -y - φ y • u) (hφu : φ u = 1) (hgu : φ (g u) = 0)
    (hp : φ (g⁻¹ u) ≠ 0) :
    IsTransvectionWith ((z * (g * z * g⁻¹)) ^ 2) (φ (g⁻¹ u) • g u) φ := by
  set p := φ (g⁻¹ u) with hpdef
  set u' := g u with hu'def
  have hu0 : u ≠ 0 := fun h => by rw [h, map_zero] at hφu; exact zero_ne_one hφu
  have hu'0 : u' ≠ 0 := fun h => hu0 (by
    have : g⁻¹ u' = u := by
      rw [hu'def]; change g.symm (g u) = u; rw [LinearEquiv.symm_apply_apply]
    rw [← this, h, map_zero])
  have hψu' : φ (g⁻¹ u') = 1 := by
    rw [hu'def]; change φ (g.symm (g u)) = 1; rw [LinearEquiv.symm_apply_apply, hφu]
  have hz' : ∀ y, (g * z * g⁻¹) y = -y - φ (g⁻¹ y) • u' := by
    intro y
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hz, map_sub, map_neg, map_smul]
    congr 2
    change g (g.symm y) = y
    rw [LinearEquiv.apply_symm_apply]
  have ht : ∀ y, (z * (g * z * g⁻¹)) y = y + φ y • u + φ (g⁻¹ y) • u' := by
    intro y
    rw [LinearEquiv.mul_apply, hz', map_sub, map_neg, map_smul, hz, hz, hgu, zero_smul,
      sub_zero]
    module
  have hψlin : ∀ a b : V, φ (g⁻¹ (a + b)) = φ (g⁻¹ a) + φ (g⁻¹ b) := fun a b => by
    rw [map_add, map_add]
  have hψsmul : ∀ (c : ZMod 3) (a : V), φ (g⁻¹ (c • a)) = c * φ (g⁻¹ a) := fun c a => by
    rw [map_smul, map_smul, smul_eq_mul]
  refine ⟨smul_ne_zero hp hu'0, fun h0 => ?_, ?_, fun y => ?_⟩
  · rw [h0] at hφu
    exact zero_ne_one hφu
  · rw [map_smul, hgu, smul_zero]
  ·
    have h2 : ((z * (g * z * g⁻¹)) ^ 2) y - (y + φ y • (p • u')) =
        (3 : ℕ) • (φ y • u + φ (g⁻¹ y) • u') := by
      rw [pow_two, LinearEquiv.mul_apply, ht y, ht, map_add, map_add, map_smul, map_smul, hφu,
        hgu, hψlin, hψlin, hψsmul, hψsmul, hψu', ← hpdef]
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
      module
    rw [zmod3_three_smul, sub_eq_zero] at h2
    rw [h2, smul_smul, mul_comm]

theorem exists_quaternion_elements {H : Type*} [Group H] (e : H ≃* QuaternionGroup 2) :
    ∃ z h₀ : H, z ≠ 1 ∧ z * z = 1 ∧ (∀ h, h * z = z * h) ∧ h₀ * h₀ = z := by
  refine ⟨e.symm (QuaternionGroup.a 2), e.symm (QuaternionGroup.a 1), ?_, ?_, fun h => ?_, ?_⟩
  · rw [Ne, MulEquiv.symm_apply_eq, map_one]
    decide
  · rw [← map_mul, show (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1 by
      decide, map_one]
  · apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (by decide : ∀ q : QuaternionGroup 2,
      q * QuaternionGroup.a 2 = QuaternionGroup.a 2 * q) _
  · rw [← map_mul, show (QuaternionGroup.a 1 * QuaternionGroup.a 1 : QuaternionGroup 2) =
      QuaternionGroup.a 2 by decide]

variable [FiniteDimensional (ZMod 3) V]

omit [FiniteDimensional (ZMod 3) V] in
theorem exists_functional_of_quaternion (hV : finrank (ZMod 3) V = 3)
    {H : Subgroup (V ≃ₗ[ZMod 3] V)} {z h₀ : V ≃ₗ[ZMod 3] V} (hzH : z ∈ H) (hz1 : z ≠ 1)
    (hzz : z * z = 1) (hzc : ∀ h ∈ H, h * z = z * h) (hh₀z : h₀ * h₀ = z) {u : V}
    (hu : u ≠ 0) (huH : ∀ h ∈ H, h u = u) :
    ∃ φ : Dual (ZMod 3) V, φ u = 1 ∧ (∀ y, z y = -y - φ y • u) ∧
      ∀ y, y ∈ commutatorSpace H ↔ φ y = 0 := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, z v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hz1 (LinearEquiv.ext hcon)
  have hzz' : ∀ y, z (z y) = y := fun y => by
    rw [← LinearEquiv.mul_apply, hzz, LinearEquiv.coe_one, id]
  set w := z v - v with hwdef
  have hzw : z w = -w := by rw [hwdef, map_sub, hzz', neg_sub]
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hv
  have hzh₀ : ∀ y, z (h₀ y) = h₀ (z y) := fun y => by
    rw [← hh₀z, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  have hzhw : z (h₀ w) = -h₀ w := by rw [hzh₀, hzw, map_neg]
  have hhhw : h₀ (h₀ w) = -w := by rw [← LinearEquiv.mul_apply, hh₀z, hzw]
  have hzu : z u = u := huH z hzH
  have hli : LinearIndependent (ZMod 3) ![w, h₀ w, u] := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    rw [Fin.sum_univ_three] at hc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hc
    have hz' := congrArg z hc
    rw [map_add, map_add, map_smul, map_smul, map_smul, hzw, hzhw, hzu, map_zero] at hz'
    have h2 : (c 2 + c 2) • u = 0 := by
      have : (c 2 + c 2) • u =
          (c 0 • w + c 1 • h₀ w + c 2 • u) + (c 0 • -w + c 1 • -h₀ w + c 2 • u) := by module
      rw [this, hc, hz', add_zero]
    have hc2 : c 2 = 0 := by
      rcases smul_eq_zero.mp h2 with h | h
      · exact (by decide : ∀ c : ZMod 3, c + c = 0 → c = 0) _ h
      · exact absurd h hu
    rw [hc2, zero_smul, add_zero] at hc
    obtain ⟨hc0, hc1⟩ := LinearIndependent.pair_iff.mp
      (linearIndependent_pair_of_apply_apply_eq_neg hw0 hhhw) _ _ hc
    intro i
    fin_cases i
    exacts [hc0, hc1, hc2]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hV])
  have hb0 : b 0 = w := by simp [b]
  have hb1 : b 1 = h₀ w := by simp [b]
  have hb2 : b 2 = u := by simp [b]
  set φ := b.coord 2 with hφdef
  have hφb : ∀ i, φ (b i) = if i = 2 then 1 else 0 := fun i => by
    rw [hφdef, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  have hφu : φ u = 1 := by rw [← hb2, hφb]; rfl
  have hφw : φ w = 0 := by rw [← hb0, hφb]; rfl
  have hφhw : φ (h₀ w) = 0 := by rw [← hb1, hφb]; rfl
  have hP2 : ∀ y, z y = -y - φ y • u := by
    have key : (z : V →ₗ[ZMod 3] V) = -LinearMap.id - φ.smulRight u := by
      refine b.ext fun i => ?_
      simp only [LinearEquiv.coe_coe, LinearMap.sub_apply, LinearMap.neg_apply,
        LinearMap.id_apply, LinearMap.smulRight_apply]
      fin_cases i
      · show z (b 0) = -b 0 - φ (b 0) • u
        rw [hb0, hzw, hφw, zero_smul, sub_zero]
      · show z (b 1) = -b 1 - φ (b 1) • u
        rw [hb1, hzhw, hφhw, zero_smul, sub_zero]
      · show z (b 2) = -b 2 - φ (b 2) • u
        rw [hb2, hzu, hφu, one_smul, zmod3_neg_sub_self]
    intro y
    have := LinearMap.congr_fun key y
    simpa using this
  have hker : ∀ y, z y = -y → φ y = 0 := fun y hy => by
    have h := hP2 y
    rw [hy] at h
    exact (smul_eq_zero.mp (sub_eq_self.mp h.symm)).resolve_right hu
  refine ⟨φ, hφu, hP2, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · have hle : commutatorSpace H ≤ LinearMap.ker φ := by
      rw [commutatorSpace, Submodule.span_le]
      rintro _ ⟨h, hh, y, rfl⟩
      apply hker
      rw [map_sub, ← LinearEquiv.mul_apply, ← hzc h hh, LinearEquiv.mul_apply, hP2 y, map_sub,
        map_neg, map_smul, huH h hh]
      abel
    exact hle hy
  · apply Submodule.subset_span
    refine ⟨z, hzH, y, ?_⟩
    rw [hP2 y, hy, zero_smul, sub_zero, zmod3_neg_sub_self]

theorem mem_span_pair_of_apply_eq_zero (hV : finrank (ZMod 3) V = 3) {φ : Dual (ZMod 3) V}
    {u : V} (hφu : φ u = 1) {w₁ w₂ : V} (h₁ : φ w₁ = 0) (h₂ : φ w₂ = 0)
    (hli : LinearIndependent (ZMod 3) ![w₁, w₂]) {v : V} (hv : φ v = 0) :
    v ∈ Submodule.span (ZMod 3) {w₁, w₂} := by
  have hker : finrank (ZMod 3) (LinearMap.ker φ) = 2 := by
    have hφ : φ ≠ 0 := fun h => by rw [h, LinearMap.zero_apply] at hφu; exact zero_ne_one hφu
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    omega
  have hle : Submodule.span (ZMod 3) {w₁, w₂} ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact h₁
    · exact h₂
  have heq := Submodule.eq_of_le_of_finrank_eq hle ((finrank_span_pair hli).trans hker.symm)
  rw [heq]
  exact hv

theorem false_of_apply_pair (hV : finrank (ZMod 3) V = 3) {φ : Dual (ZMod 3) V} {u : V}
    (hφu : φ u = 1) {x : V ≃ₗ[ZMod 3] V} (hxW : ∃ w, φ w = 0 ∧ φ (x w) ≠ 0) {w₁ w₂ : V}
    (h₁ : φ w₁ = 0) (h₂ : φ w₂ = 0) (hli : LinearIndependent (ZMod 3) ![w₁, w₂])
    (hx₁ : φ (x w₁) = 0) (hx₂ : φ (x w₂) = 0) : False := by
  obtain ⟨w, hw, hxw⟩ := hxW
  obtain ⟨a, b, rfl⟩ :=
    Submodule.mem_span_pair.mp (mem_span_pair_of_apply_eq_zero hV hφu h₁ h₂ hli hw)
  apply hxw
  simp only [map_add, map_smul, hx₁, hx₂, smul_eq_mul, mul_zero, add_zero]

section Core

variable {G : Subgroup (V ≃ₗ[ZMod 3] V)} {z h₀ x : V ≃ₗ[ZMod 3] V} {u : V}
  {φ : Dual (ZMod 3) V}

omit [FiniteDimensional (ZMod 3) V] in
theorem apply_eq_zero_of_sq_eq (hφu : φ u = 1) (hz : ∀ y, z y = -y - φ y • u)
    (hh₀z : h₀ * h₀ = z) {y : V} (hy : φ y = 0) : φ (h₀ y) = 0 := by
  have hu : u ≠ 0 := fun h => by rw [h, map_zero] at hφu; exact zero_ne_one hφu
  have h1 : z (h₀ y) = -h₀ y := by
    rw [← hh₀z, LinearEquiv.mul_apply, ← LinearEquiv.mul_apply h₀ h₀ y, hh₀z, hz y, hy,
      zero_smul, sub_zero, map_neg]
  have h2 := hz (h₀ y)
  rw [h1] at h2
  exact (smul_eq_zero.mp (sub_eq_self.mp h2.symm)).resolve_right hu

theorem irreducible_of_quaternion (hV : finrank (ZMod 3) V = 3) (hφu : φ u = 1)
    (hz : ∀ y, z y = -y - φ y • u) (hzG : z ∈ G) (hh₀G : h₀ ∈ G) (hh₀z : h₀ * h₀ = z)
    (hxG : x ∈ G) (hx3 : ∀ y, x (x (x y)) = y) (hCx : ∀ y, x y = y → φ y = 0)
    (hxW : ∃ w, φ w = 0 ∧ φ (x w) ≠ 0) (Y : Submodule (ZMod 3) V)
    (hY : ∀ g ∈ G, ∀ y ∈ Y, g y ∈ Y) : Y = ⊥ ∨ Y = ⊤ := by
  have hfill : ∀ y ∈ Y, y ≠ 0 → φ y = 0 → ∀ v, φ v = 0 → v ∈ Y := by
    intro y hy hy0 hφy v hv
    have hli := linearIndependent_pair_of_apply_apply_eq_neg (h := h₀) hy0
      (by rw [← LinearEquiv.mul_apply, hh₀z, hz, hφy, zero_smul, sub_zero])
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp
      (mem_span_pair_of_apply_eq_zero hV hφu hφy (apply_eq_zero_of_sq_eq hφu hz hh₀z hφy) hli hv)
    exact Y.add_mem (Y.smul_mem a hy) (Y.smul_mem b (hY h₀ hh₀G y hy))
  by_cases hYW : ∀ y ∈ Y, φ y = 0
  · left
    by_contra hY0
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
    obtain ⟨w, hw, hxw⟩ := hxW
    exact hxw (hYW _ (hY x hxG w (hfill y hy hy0 (hYW y hy) w hw)))
  · right
    push Not at hYW
    obtain ⟨y, hy, hφy⟩ := hYW
    have huY : u ∈ Y := by
      have h1 : φ y • u ∈ Y := by
        have : φ y • u = -y - z y := by rw [hz y]; abel
        rw [this]
        exact Y.sub_mem (Y.neg_mem hy) (hY z hzG y hy)
      have := Y.smul_mem (φ y)⁻¹ h1
      rwa [smul_smul, inv_mul_cancel₀ hφy, one_smul] at this
    obtain ⟨c, hc⟩ : ∃ c : ZMod 3, φ (x u) = c := ⟨_, rfl⟩
    have hw₁Y : x u - c • u ∈ Y := Y.sub_mem (hY x hxG u huY) (Y.smul_mem c huY)
    have hφw₁ : φ (x u - c • u) = 0 := by
      rw [map_sub, map_smul, hφu, hc, smul_eq_mul, mul_one]
      exact sub_self _
    have hw₁0 : x u - c • u ≠ 0 := by
      intro h0
      have hxu : x u = c • u := sub_eq_zero.mp h0
      have h3 : (c * c * c) • u = u := by
        calc (c * c * c) • u = x (x (x u)) := by simp only [hxu, map_smul, smul_smul, mul_assoc]
          _ = u := hx3 u
      rw [(by decide : ∀ c : ZMod 3, c * c * c = c) c, ← hxu] at h3
      have := hCx u h3
      rw [hφu] at this
      exact one_ne_zero this
    rw [eq_top_iff]
    intro v _
    have hv : v = (v - φ v • u) + φ v • u := by abel
    rw [hv]
    refine Y.add_mem (hfill _ hw₁Y hw₁0 hφw₁ _ ?_) (Y.smul_mem _ huY)
    rw [map_sub, map_smul, hφu, smul_eq_mul, mul_one]
    exact sub_self _

theorem exists_mem_apply_eq_zero (hV : finrank (ZMod 3) V = 3) (hφu : φ u = 1)
    (hz : ∀ y, z y = -y - φ y • u) (hzz : z * z = 1) (hzG : z ∈ G) (hh₀G : h₀ ∈ G)
    (hh₀z : h₀ * h₀ = z) (hh₀u : h₀ u = u) (hxG : x ∈ G) (hx3 : ∀ y, x (x (x y)) = y)
    (hCx : ∀ y, x y = y → φ y = 0) (hxW : ∃ w, φ w = 0 ∧ φ (x w) ≠ 0) :
    ∃ g ∈ G, φ (g u) = 0 ∧ φ (g⁻¹ u) ≠ 0 := by
  have hxinv : ∀ y, x⁻¹ y = x (x y) := fun y => by
    change x.symm y = _
    rw [LinearEquiv.symm_apply_eq, hx3]
  have hs : φ u + φ (x u) + φ (x (x u)) = 0 := by
    rw [← map_add, ← map_add]
    apply hCx
    rw [map_add, map_add, hx3]
    abel
  rw [hφu] at hs
  rcases (by decide : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = 2) (φ (x u)) with hp | hp | hp
  ·
    refine ⟨x, hxG, hp, ?_⟩
    rw [hxinv]
    rw [hp] at hs
    exact (by decide : ∀ q : ZMod 3, 1 + 0 + q = 0 → q ≠ 0) _ hs
  ·
    rw [hp] at hs
    have hzu : z u = u := by rw [hz, hφu, one_smul, zmod3_neg_sub_self]
    set w₀ := x u - u with hw₀def
    have hφw₀ : φ w₀ = 0 := by rw [hw₀def, map_sub, hp, hφu]; exact sub_self _
    have hw₀0 : w₀ ≠ 0 := fun h => by
      have := hCx u (sub_eq_zero.mp h)
      rw [hφu] at this
      exact one_ne_zero this
    have hxw₀ : x w₀ = w₀ := by
      set s := u + x u + x (x u) with hsdef
      have hxs : x s = s := by rw [hsdef, map_add, map_add, hx3]; abel
      have hφs : φ s = 0 := hCx s hxs
      have hxw₀s : x w₀ = w₀ + s := by
        rw [hw₀def, hsdef, map_sub, ← sub_eq_zero,
          show x (x u) - x u - (x u - u + (u + x u + x (x u))) = -((3 : ℕ) • x u) by abel,
          zmod3_three_smul, neg_zero]
      by_contra hne
      have hs0 : s ≠ 0 := fun h => hne (by rw [hxw₀s, h, add_zero])
      have hli : LinearIndependent (ZMod 3) ![w₀, s] :=
        LinearIndependent.pair_iff.mpr fun a c hac => by
          have h1 := congrArg x hac
          rw [map_add, map_smul, map_smul, hxw₀s, hxs, map_zero] at h1
          have h2 : a • s = 0 := by
            have : a • s = a • (w₀ + s) + c • s - (a • w₀ + c • s) := by module
            rw [this, h1, hac, sub_zero]
          have ha : a = 0 := (smul_eq_zero.mp h2).resolve_right hs0
          rw [ha, zero_smul, zero_add] at hac
          exact ⟨ha, (smul_eq_zero.mp hac).resolve_right hs0⟩
      exact false_of_apply_pair hV hφu hxW hφw₀ hφs hli
        (by rw [hxw₀s, map_add, hφw₀, hφs, add_zero]) (by rw [hxs, hφs])
    have hφh₀w₀ : φ (h₀ w₀) = 0 := apply_eq_zero_of_sq_eq hφu hz hh₀z hφw₀
    have hli₀ : LinearIndependent (ZMod 3) ![w₀, h₀ w₀] :=
      linearIndependent_pair_of_apply_apply_eq_neg hw₀0
        (by rw [← LinearEquiv.mul_apply, hh₀z, hz, hφw₀, zero_smul, sub_zero])
    have hq : φ (x (h₀ w₀)) ≠ 0 := fun hq =>
      false_of_apply_pair hV hφu hxW hφw₀ hφh₀w₀ hli₀ (by rw [hxw₀, hφw₀]) hq
    obtain ⟨h, hhG, hhz, hhu, hxhw₀⟩ : ∃ h ∈ G, h * h = z ∧ h u = u ∧ φ (x (h w₀)) = 1 := by
      rcases (by decide : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = 2) _ hq with hq1 | hq2
      · exact ⟨h₀, hh₀G, hh₀z, hh₀u, hq1⟩
      · have hzh : z * h₀ = h₀ * z := by rw [← hh₀z, mul_assoc]
        refine ⟨z * h₀, G.mul_mem hzG hh₀G, ?_, ?_, ?_⟩
        · rw [mul_assoc, ← mul_assoc h₀, ← hzh, ← mul_assoc, ← mul_assoc, hzz, one_mul, hh₀z]
        · rw [LinearEquiv.mul_apply, hh₀u, hzu]
        · rw [LinearEquiv.mul_apply, hz (h₀ w₀), hφh₀w₀, zero_smul, sub_zero, map_neg, map_neg,
            hq2]
          decide
    have hxinvu : x⁻¹ u = u - w₀ := by
      change x.symm u = _
      rw [LinearEquiv.symm_apply_eq, map_sub, hxw₀, hw₀def, sub_sub_cancel]
    have hhinvu : h⁻¹ u = u := by
      change h.symm u = u
      rw [LinearEquiv.symm_apply_eq, hhu]
    have hhinvw₀ : h⁻¹ w₀ = -h w₀ := by
      change h.symm w₀ = -h w₀
      rw [LinearEquiv.symm_apply_eq, map_neg, ← LinearEquiv.mul_apply, hhz, hz, hφw₀, zero_smul,
        sub_zero, neg_neg]
    refine ⟨x * h * x⁻¹, G.mul_mem (G.mul_mem hxG hhG) (G.inv_mem hxG), ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxinvu, map_sub, hhu, map_sub, map_sub,
        hp, hxhw₀]
      exact sub_self _
    · rw [mul_inv_rev, mul_inv_rev, inv_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        hxinvu, map_sub, hhinvu, hhinvw₀, sub_neg_eq_add, map_add, map_add, hp, hxhw₀]
      decide
  ·
    refine ⟨x⁻¹, G.inv_mem hxG, ?_, ?_⟩
    · rw [hxinv]
      rw [hp] at hs
      exact (by decide : ∀ q : ZMod 3, 1 + 2 + q = 0 → q = 0) _ hs
    · rw [inv_inv, hp]
      decide

end Core

theorem rank3II_3_13 (hV : finrank (ZMod 3) V = 3) {G H : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hHG : H ≤ G) (hH : Nonempty (H ≃* QuaternionGroup 2))
    (hCH : ∃ u : V, u ≠ 0 ∧ ∀ h ∈ H, h u = u) {x : V ≃ₗ[ZMod 3] V} (hxG : x ∈ G)
    (hx : orderOf x = 3) (hCx : ∀ v, x v = v → v ∈ commutatorSpace H)
    (hxW : ∃ w ∈ commutatorSpace H, x w - w ∉ commutatorSpace H) :
    G = (LinearEquiv.det : (V ≃ₗ[ZMod 3] V) →* (ZMod 3)ˣ).ker ∨ G = ⊤ := by
  obtain ⟨e⟩ := hH
  obtain ⟨z, h₀, hz1, hzz, hzc, hh₀z⟩ := exists_quaternion_elements e
  obtain ⟨u, hu, huH⟩ := hCH
  obtain ⟨φ, hφu, hz, hW⟩ := exists_functional_of_quaternion hV z.2
    (fun h => hz1 (Subtype.ext h)) (congrArg Subtype.val hzz)
    (fun h hh => congrArg Subtype.val (hzc ⟨h, hh⟩)) (congrArg Subtype.val hh₀z) hu huH
  have hx3 : ∀ y, x (x (x y)) = y := fun y => by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    have : (x ^ 3) y = y := by rw [h, LinearEquiv.coe_one, id]
    rwa [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
  have hCx' : ∀ y, x y = y → φ y = 0 := fun y hy => (hW y).mp (hCx y hy)
  have hxW' : ∃ w, φ w = 0 ∧ φ (x w) ≠ 0 := by
    obtain ⟨w, hw, hxw⟩ := hxW
    have hφw := (hW w).mp hw
    refine ⟨w, hφw, fun h => hxw ((hW _).mpr ?_)⟩
    rw [map_sub, h, hφw]
    exact sub_zero _
  have hzG : (z : V ≃ₗ[ZMod 3] V) ∈ G := hHG z.2
  have hh₀G : (h₀ : V ≃ₗ[ZMod 3] V) ∈ G := hHG h₀.2
  have hh₀z' : (h₀ : V ≃ₗ[ZMod 3] V) * h₀ = z := congrArg Subtype.val hh₀z
  obtain ⟨g, hgG, hgu, hgu'⟩ := exists_mem_apply_eq_zero hV hφu hz (congrArg Subtype.val hzz)
    hzG hh₀G hh₀z' (huH _ h₀.2) hxG hx3 hCx' hxW'
  have htG : ((z : V ≃ₗ[ZMod 3] V) * (g * z * g⁻¹)) ^ 2 ∈ G :=
    G.pow_mem (G.mul_mem hzG (G.mul_mem (G.mul_mem hgG hzG) (G.inv_mem hgG))) 2
  have hSL := det_eq_one_mem_of_irreducible hV G
    (irreducible_of_quaternion hV hφu hz hzG hh₀G hh₀z' hxG hx3 hCx' hxW') htG
    (isTransvectionWith_sq_mul_conj hz hφu hgu hgu')
  by_cases hdet : ∀ g ∈ G, LinearMap.det (g : V →ₗ[ZMod 3] V) = 1
  · left
    ext g
    rw [MonoidHom.mem_ker, ← Units.val_eq_one, LinearEquiv.coe_det]
    exact ⟨hdet g, hSL g⟩
  · right
    push Not at hdet
    obtain ⟨g₁, hg₁G, hg₁⟩ := hdet
    rw [eq_top_iff]
    intro g _
    by_cases hg : LinearMap.det (g : V →ₗ[ZMod 3] V) = 1
    · exact hSL g hg
    · have h2 : ∀ k : V ≃ₗ[ZMod 3] V, LinearMap.det (k : V →ₗ[ZMod 3] V) ≠ 1 →
          (LinearEquiv.det k : ZMod 3) = 2 := fun k hk => by
        have h0 : (LinearEquiv.det k : ZMod 3) ≠ 0 := Units.ne_zero _
        rw [LinearEquiv.coe_det] at h0 ⊢
        exact (by decide : ∀ a : ZMod 3, a ≠ 0 → a ≠ 1 → a = 2) _ h0 hk
      have heq : LinearEquiv.det g = LinearEquiv.det g₁ :=
        Units.ext ((h2 g hg).trans (h2 g₁ hg₁).symm)
      have hmem : g₁⁻¹ * g ∈ G := hSL _ (by
        rw [← LinearEquiv.coe_det, map_mul, map_inv, heq, inv_mul_cancel, Units.val_one])
      have := G.mul_mem hg₁G hmem
      rwa [mul_inv_cancel_left] at this

end CFSG.RankThree.PartTwo.Sec3
