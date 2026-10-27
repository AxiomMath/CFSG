module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ParFact2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace L34G

variable {k : Type} [Field k]

theorem map_apply (σ : k ≃+* k) (g : SpecialLinearGroup (Fin 3) k) (i j : Fin 3) :
    ((SpecialLinearGroup.map σ.toRingHom g : SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) i j = σ ((g : Matrix (Fin 3) (Fin 3) k) i j) := by
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

theorem map_mem_upperTriangular (σ : k ≃+* k) {g : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ upperTriangular 3 k) :
    SpecialLinearGroup.map σ.toRingHom g ∈ upperTriangular 3 k := fun i j hij => by
  rw [map_apply, hg i j hij, map_zero]

theorem map_mem_unitriangular (σ : k ≃+* k) {g : SpecialLinearGroup (Fin 3) k}
    (hg : g ∈ unitriangular 3 k) :
    SpecialLinearGroup.map σ.toRingHom g ∈ unitriangular 3 k :=
  ⟨map_mem_upperTriangular σ hg.1, fun i => by rw [map_apply, hg.2 i, map_one]⟩

theorem fieldAut_mem_projUpperTriangular (σ : k ≃+* k) {x : projectiveSL 3 k}
    (hx : x ∈ projUpperTriangular 3 k) : fieldAut 3 k σ x ∈ projUpperTriangular 3 k := by
  obtain ⟨g, hg, rfl⟩ := hx
  rw [fieldAut_proj]
  exact ⟨_, map_mem_upperTriangular σ hg, rfl⟩

theorem fieldAut_mem_projUnitriangular (σ : k ≃+* k) {x : projectiveSL 3 k}
    (hx : x ∈ projUnitriangular 3 k) : fieldAut 3 k σ x ∈ projUnitriangular 3 k := by
  obtain ⟨g, hg, rfl⟩ := hx
  rw [fieldAut_proj]
  exact ⟨_, map_mem_unitriangular σ hg, rfl⟩

theorem chiP_fieldAut {σ : k ≃+* k} (hσ : ∀ a, σ a = a ^ 2) (x : projUpperTriangular 3 k) :
    KGL34P.chiP (⟨fieldAut 3 k σ x, fieldAut_mem_projUpperTriangular σ x.2⟩ :
      projUpperTriangular 3 k) = KGL34P.chiP x ^ 2 := by
  obtain ⟨g, rfl⟩ := KGL34P.projB_surjective x
  have he : (⟨fieldAut 3 k σ (KGL34P.projB g), fieldAut_mem_projUpperTriangular σ
      (KGL34P.projB g).2⟩ : projUpperTriangular 3 k) =
      KGL34P.projB ⟨_, map_mem_upperTriangular σ g.2⟩ := by
    apply Subtype.ext
    exact fieldAut_proj σ _
  rw [he, KGL34P.chiP_projB, KGL34P.chiP_projB]
  apply Units.ext
  rw [KGL34P.val_chiB, Units.val_pow_eq_pow_val, KGL34P.val_chiB, map_apply, map_apply, hσ, hσ]
  ring

theorem map_rad (σ : k ≃+* k) (b c : k) :
    SpecialLinearGroup.map σ.toRingHom (KGL34P.rad b c) = KGL34P.rad (σ b) (σ c) := by
  apply Subtype.ext
  ext i j
  rw [map_apply, KGL34P.coe_rad, KGL34P.coe_rad]
  fin_cases i <;> fin_cases j <;> simp

theorem map_radP_fieldAut [Finite k] (σ : k ≃+* k) :
    (KGL34P.radP (k := k)).map (fieldAut 3 k σ).toMonoidHom = KGL34P.radP := by
  have hle : (KGL34P.radP (k := k)).map (fieldAut 3 k σ).toMonoidHom ≤ KGL34P.radP := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨b, c, rfl⟩ := KGL34P.mem_radP.mp hx
    show fieldAut 3 k σ (proj 3 k (KGL34P.rad b c)) ∈ _
    rw [fieldAut_proj, map_rad]
    exact KGL34P.mem_radP.mpr ⟨_, _, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (fieldAut 3 k σ).injective).ge

theorem map_inv_eq {β : MulAut (projectiveSL 3 k)} {H : Subgroup (projectiveSL 3 k)}
    (h : H.map β.toMonoidHom = H) : H.map β⁻¹.toMonoidHom = H := by
  conv_lhs => rw [← h]
  rw [KGL34P.map_map_mulAut, inv_mul_cancel]
  exact Subgroup.map_id _

theorem map_mul_eq {β γ : MulAut (projectiveSL 3 k)} {H : Subgroup (projectiveSL 3 k)}
    (hβ : H.map β.toMonoidHom = H) (hγ : H.map γ.toMonoidHom = H) :
    H.map (β * γ).toMonoidHom = H := by
  rw [← KGL34P.map_map_mulAut, hγ, hβ]

theorem mem_normalizer_iff {g : projectiveSL 3 k} {H : Subgroup (projectiveSL 3 k)} :
    g ∈ Subgroup.normalizer (H : Set (projectiveSL 3 k)) ↔
      H.map (MulAut.conj g).toMonoidHom = H :=
  Subgroup.mem_normalizer_iff_map_conj_eq

variable (hk : Nat.card k = 4)
include hk

theorem map_conj_radP {g : projectiveSL 3 k} (hg : g ∈ projUpperTriangular 3 k) :
    (KGL34P.radP (k := k)).map (MulAut.conj g).toMonoidHom = KGL34P.radP := by
  refine mem_normalizer_iff.mp ?_
  rw [KGL34P.normalizer_radP hk]
  exact projUpperTriangular_le_projStabilizer 1 hg

theorem radP_ne_map_alpha0 :
    KGL34P.radP ≠ (KGL34P.radP (k := k)).map (KGL34P.alpha0Aut hk).toMonoidHom := by
  have hN2 : Subgroup.normalizer (((KGL34P.radP (k := k)).map
      (KGL34P.alpha0Aut hk).toMonoidHom : Subgroup (projectiveSL 3 k)) :
        Set (projectiveSL 3 k)) = projStabilizer (flagSpace 3 k 2) := by
    rw [← Subgroup.map_equiv_normalizer_eq, KGL34P.normalizer_radP hk,
      KGL34P.map_projStabilizer_one_alpha0 hk]
  intro h
  apply KGL34P.projStabilizer_one_ne_two hk
  rw [← KGL34P.normalizer_radP hk, ← hN2, ← h]

theorem map_radP_of_pow_three {β : MulAut (projectiveSL 3 k)} (hβ3 : β ^ 3 = 1)
    (hβU : (projUnitriangular 3 k).map β.toMonoidHom = projUnitriangular 3 k) :
    (KGL34P.radP (k := k)).map β.toMonoidHom = KGL34P.radP := by
  have hne := radP_ne_map_alpha0 hk
  rcases KGL34P.map_radP_mem hk hβU with h | h
  · exact h
  · exfalso
    rcases KGL34P.map_radP_mem hk (map_mul_eq hβU (KGL34P.alpha0Aut_map_projUnitriangular hk))
      with h' | h'
    ·
      have e1 : ((KGL34P.radP (k := k)).map (KGL34P.alpha0Aut hk).toMonoidHom).map
          β.toMonoidHom = KGL34P.radP := by
        rw [KGL34P.map_map_mulAut]
        exact h'
      have e3 : (KGL34P.radP (k := k)).map (β ^ 3).toMonoidHom =
          (KGL34P.radP (k := k)).map (KGL34P.alpha0Aut hk).toMonoidHom := by
        rw [pow_three, ← KGL34P.map_map_mulAut, ← KGL34P.map_map_mulAut, h, e1, h]
      rw [hβ3] at e3
      exact hne ((Subgroup.map_id _).symm.trans e3)
    ·
      have e1 : ((KGL34P.radP (k := k)).map (KGL34P.alpha0Aut hk).toMonoidHom).map
          β.toMonoidHom = (KGL34P.radP (k := k)).map β.toMonoidHom := by
        rw [KGL34P.map_map_mulAut, h', h]
      exact hne (Subgroup.map_injective (f := β.toMonoidHom) β.injective e1).symm

theorem exists_mem_projUpperTriangular_not_mem :
    ∃ b ∈ projUpperTriangular 3 k, b ∉ projUnitriangular 3 k := by
  obtain ⟨ω, hω0, hω1⟩ := LinearFieldFour.exists_ne_zero_ne_one hk
  have hω3 : ω ^ 3 = 1 := KGL34P.pow_three_eq_one_of_ne_zero hk hω0
  have hT : KGL34P.torusDiag ω hω3 ∈ upperTriangular 3 k := by
    intro i j hij
    rw [KGL34P.coe_torusDiag]
    fin_cases i <;> fin_cases j <;> simp_all
  refine ⟨_, ⟨_, hT, rfl⟩, fun hU => ?_⟩
  have h1 := (KGL34P.chiP_eq_one_iff hk (KGL34P.projB ⟨_, hT⟩)).mpr hU
  rw [KGL34P.chiP_projB] at h1
  have h3 : ((KGL34P.torusDiag ω hω3 : SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) 0 0 = 1 := by
    rw [KGL34P.coe_torusDiag]
    rfl
  have h4 : ((KGL34P.torusDiag ω hω3 : SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) 2 2 = ω ^ 2 := by
    rw [KGL34P.coe_torusDiag]
    rfl
  have h2 : ((KGL34P.torusDiag ω hω3 : SpecialLinearGroup (Fin 3) k) :
      Matrix (Fin 3) (Fin 3) k) 0 0 * (((KGL34P.torusDiag ω hω3 : SpecialLinearGroup (Fin 3) k) :
        Matrix (Fin 3) (Fin 3) k) 2 2)⁻¹ = 1 := by
    have := congrArg Units.val h1
    rwa [KGL34P.val_chiB, Units.val_one] at this
  rw [h3, h4, one_mul, inv_eq_one] at h2
  apply hω1
  linear_combination hω3 - ω * h2

theorem right_inverts {u v : KGL34P.OutL34 k} (hu3 : u ^ 3 = 1) (hu1 : u ≠ 1)
    (hvu : v * u = u⁻¹ * v) :
    u.right = 1 ∧ Multiplicative.toAdd v.right.1 + Multiplicative.toAdd v.right.2 ≠ 0 := by
  have hwr : ∀ w : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), w * w = 1 := by
    rintro ⟨a, b⟩
    refine Prod.ext ?_ ?_ <;>
      exact Multiplicative.toAdd.injective (by simp [CharTwo.add_self_eq_zero])
  have hr : u.right = 1 := by
    have h3 := congrArg SemidirectProduct.right hu3
    rw [SemidirectProduct.one_right, pow_three, SemidirectProduct.mul_right,
      SemidirectProduct.mul_right, hwr, mul_one] at h3
    exact h3
  refine ⟨hr, fun hw => hu1 ?_⟩
  have hl := congrArg SemidirectProduct.left hvu
  simp only [SemidirectProduct.mul_left, SemidirectProduct.inv_left, SemidirectProduct.inv_right,
    hr] at hl
  rw [KGL34P.inversionAction_eq] at hl
  simp only [hw, ↓reduceIte] at hl
  rw [mul_comm] at hl
  have h1 : u.left = u.left⁻¹ := mul_right_cancel hl
  have h2 : u.left ^ 2 = 1 := by
    rw [sq]
    nth_rewrite 1 [h1]
    exact inv_mul_cancel _
  have h3 : u.left ^ 3 = 1 := LinearThreeFourOuter.units_pow_three hk u.left
  refine SemidirectProduct.ext ?_ hr
  calc u.left = u.left ^ 3 * (u.left ^ 2)⁻¹ := by group
    _ = 1 := by rw [h2, h3, inv_one, one_mul]

theorem centB_mul {α β : MulAut (projectiveSL 3 k)}
    (hαB : ∀ b ∈ projUpperTriangular 3 k, α b * b⁻¹ ∈ projUnitriangular 3 k)
    (hβU : (projUnitriangular 3 k).map β.toMonoidHom = projUnitriangular 3 k)
    (hβB : ∀ b ∈ projUpperTriangular 3 k, β b * b⁻¹ ∈ projUnitriangular 3 k) :
    ∀ b ∈ projUpperTriangular 3 k, (α * β) b * b⁻¹ ∈ projUnitriangular 3 k := by
  intro b hb
  have hβb : β b ∈ projUpperTriangular 3 k := by
    rw [← KGL34P.map_projUpperTriangular hk hβU]
    exact ⟨b, hb, rfl⟩
  have e : (α * β) b * b⁻¹ = (α (β b) * (β b)⁻¹) * (β b * b⁻¹) := by
    rw [MulAut.mul_apply]
    group
  rw [e]
  exact mul_mem (hαB _ hβb) (hβB b hb)

theorem centB_pow {β : MulAut (projectiveSL 3 k)}
    (hβU : (projUnitriangular 3 k).map β.toMonoidHom = projUnitriangular 3 k)
    (hβB : ∀ b ∈ projUpperTriangular 3 k, β b * b⁻¹ ∈ projUnitriangular 3 k) (j : ℕ) :
    ∀ b ∈ projUpperTriangular 3 k, (β ^ j) b * b⁻¹ ∈ projUnitriangular 3 k := by
  induction j with
  | zero =>
    intro b _
    rw [pow_zero, MulAut.one_apply, mul_inv_cancel]
    exact one_mem _
  | succ j ih =>
    rw [pow_succ]
    exact centB_mul hk ih hβU hβB

theorem map_radP_ne {α β : MulAut (projectiveSL 3 k)} (hβ3 : β ^ 3 = 1)
    (hαU : (projUnitriangular 3 k).map α.toMonoidHom = projUnitriangular 3 k)
    (hβU : (projUnitriangular 3 k).map β.toMonoidHom = projUnitriangular 3 k)
    (hαβ : α * β * α⁻¹ = β⁻¹)
    (hαB : ∀ b ∈ projUpperTriangular 3 k, α b * b⁻¹ ∈ projUnitriangular 3 k)
    (hβB : ∀ b ∈ projUpperTriangular 3 k, β b * b⁻¹ ∈ projUnitriangular 3 k)
    (hβ : β ∉ (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range) :
    (KGL34P.radP (k := k)).map α.toMonoidHom ≠ KGL34P.radP := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hk
  have hker := LinearThreeFourOuter.ker_eq_range_conj hσ hk hΨ
  have hNU := normalizer_projUnitriangular (n := 3) (K := k) 2
  set f := fieldAut 3 k (frobeniusEquiv k 2) with hf
  have hfU : (projUnitriangular 3 k).map f.toMonoidHom = projUnitriangular 3 k :=
    KGL34P.map_projUnitriangular_eq fun x hx => fieldAut_mem_projUnitriangular _ hx
  have hΨf : Ψ f = ⟨1, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 0)⟩ := by
    rw [hf, ← LinearThreeFourOuter.nf_one_zero, hΨ, map_one]
  set α₀ := KGL34P.alpha0Aut hk with hα₀
  have hα₀U := KGL34P.alpha0Aut_map_projUnitriangular hk
  have hΨ0 : Ψ α₀ = ⟨1, (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)⟩ := by
    show Ψ (LinearThreeFourOuter.nf (frobeniusEquiv k 2) KGL34P.w0GL 1 1) = _
    rw [hΨ, KGL34P.det_w0GL hk]
  have hu3 : Ψ β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hu1 : Ψ β ≠ 1 := fun h1 => hβ (hker ▸ MonoidHom.mem_ker.mpr h1)
  have hvu : Ψ α * Ψ β = (Ψ β)⁻¹ * Ψ α := by
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    calc α * β = α * β * α⁻¹ * α := by group
      _ = β⁻¹ * α := by rw [hαβ]
  obtain ⟨hur, hw⟩ := right_inverts hk hu3 hu1 hvu
  have hua : Ψ β = SemidirectProduct.inl (Ψ β).left := SemidirectProduct.ext rfl hur
  have ha1 : (Ψ β).left ≠ 1 := fun h => hu1 (by rw [hua, h, map_one])
  have hord : orderOf (Ψ β).left = 3 :=
    orderOf_eq_prime (LinearThreeFourOuter.units_pow_three hk _) ha1
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (Ψ β).left ^ j = (Ψ α).left := by
    have htop : Subgroup.zpowers (Ψ β).left = ⊤ := Subgroup.eq_top_of_card_eq _ (by
      rw [Nat.card_zpowers, hord, LinearThreeFourOuter.card_units_eq_three hk])
    have h1 : (Ψ α).left ∈ Subgroup.zpowers (Ψ β).left := htop ▸ Subgroup.mem_top _
    have h2 : (Ψ α).left ∈ (Submonoid.powers (Ψ β).left : Set kˣ) := by
      rw [powers_eq_zpowers]
      exact h1
    exact (Submonoid.mem_powers_iff _ _).mp h2
  set γ := α * β ^ j with hγ
  have hΨγ : Ψ γ = ⟨1, (Ψ α).right⟩ := by
    rw [hγ, map_mul, map_pow, hua, ← map_pow SemidirectProduct.inl]
    refine SemidirectProduct.ext ?_ ?_
    · rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl]
      simp only [KGL34P.inversionAction_eq, hw, ↓reduceIte]
      rw [hj, mul_inv_cancel]
    · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, mul_one]
  have hγU : (projUnitriangular 3 k).map γ.toMonoidHom = projUnitriangular 3 k :=
    map_mul_eq hαU (KGL34P.map_pow_eq_of_map_eq hβU j)
  have hγB := centB_mul hk hαB (KGL34P.map_pow_eq_of_map_eq hβU j) (centB_pow hk hβU hβB j)
  obtain ⟨⟨x, y⟩, hxy⟩ : ∃ w, (Ψ α).right = w := ⟨_, rfl⟩
  rw [hxy] at hw hΨγ
  have field : Multiplicative.toAdd x = 1 → Multiplicative.toAdd y = 0 → False := by
    intro hx hy
    have ex : x = Multiplicative.ofAdd 1 := by rw [← hx]; rfl
    have ey : y = Multiplicative.ofAdd 0 := by rw [← hy]; rfl
    obtain ⟨g, hg⟩ : γ * f⁻¹ ∈
        (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hΨγ, hΨf, ex, ey, mul_inv_cancel]
    have hγf : γ = MulAut.conj g * f := by rw [hg, inv_mul_cancel_right]
    have hgB : g ∈ projUpperTriangular 3 k := by
      rw [← hNU, mem_normalizer_iff, hg]
      exact map_mul_eq hγU (map_inv_eq hfU)
    obtain ⟨b, hb, hbU⟩ := exists_mem_projUpperTriangular_not_mem hk
    have hfb : f b ∈ projUpperTriangular 3 k := fieldAut_mem_projUpperTriangular _ hb
    have hmem : γ b * b⁻¹ ∈ projUpperTriangular 3 k := by
      rw [hγf, MulAut.mul_apply, MulAut.conj_apply]
      exact mul_mem (mul_mem (mul_mem hgB hfb) (inv_mem hgB)) (inv_mem hb)
    have hsub : (⟨γ b * b⁻¹, hmem⟩ : projUpperTriangular 3 k) =
        ⟨g, hgB⟩ * ⟨f b, hfb⟩ * (⟨g, hgB⟩ : projUpperTriangular 3 k)⁻¹ *
          (⟨b, hb⟩ : projUpperTriangular 3 k)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hγf, MulAut.mul_apply, MulAut.conj_apply]
    have hχ1 : KGL34P.chiP (⟨γ b * b⁻¹, hmem⟩ : projUpperTriangular 3 k) = 1 :=
      (KGL34P.chiP_eq_one_iff hk _).mpr (hγB b hb)
    have hχf : KGL34P.chiP (⟨f b, hfb⟩ : projUpperTriangular 3 k) =
        KGL34P.chiP (⟨b, hb⟩ : projUpperTriangular 3 k) ^ 2 := chiP_fieldAut hσ ⟨b, hb⟩
    rw [hsub, map_mul, map_mul, map_mul, map_inv, map_inv, hχf] at hχ1
    have hχb : KGL34P.chiP (⟨b, hb⟩ : projUpperTriangular 3 k) = 1 := by
      rw [← hχ1, mul_comm (KGL34P.chiP _) (KGL34P.chiP _ ^ 2)]
      group
    exact hbU ((KGL34P.chiP_eq_one_iff hk _).mp hχb)
  have graph : Multiplicative.toAdd x = 0 → Multiplicative.toAdd y = 1 →
      (KGL34P.radP (k := k)).map α.toMonoidHom ≠ KGL34P.radP := by
    intro hx hy hαR
    have ex : x = Multiplicative.ofAdd 0 := by rw [← hx]; rfl
    have ey : y = Multiplicative.ofAdd 1 := by rw [← hy]; rfl
    have hΨ0f : Ψ (α₀ * f) = ⟨1, (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)⟩ := by
      rw [map_mul, hΨ0, hΨf]
      refine SemidirectProduct.ext ?_ ?_
      · rw [SemidirectProduct.mul_left]
        show (1 : kˣ) * (LinearThreeFourOuter.inversionAction kˣ
          (Multiplicative.ofAdd 1, Multiplicative.ofAdd 1)) 1 = 1
        rw [map_one (LinearThreeFourOuter.inversionAction kˣ _), one_mul]
      · rw [SemidirectProduct.mul_right]
        show (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1,
          Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 0) =
            (Multiplicative.ofAdd 0, Multiplicative.ofAdd 1)
        rw [← ofAdd_add, ← ofAdd_add, show (1 + 1 : ZMod 2) = 0 from rfl, add_zero]
    obtain ⟨g, hg⟩ : γ * (α₀ * f)⁻¹ ∈
        (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hΨγ, hΨ0f, ex, ey, mul_inv_cancel]
    have hγg : γ = MulAut.conj g * (α₀ * f) := by rw [hg, inv_mul_cancel_right]
    have hgB : g ∈ projUpperTriangular 3 k := by
      rw [← hNU, mem_normalizer_iff, hg]
      exact map_mul_eq hγU (map_inv_eq (map_mul_eq hα₀U hfU))
    have hβR := map_radP_of_pow_three hk hβ3 hβU
    have hγR : (KGL34P.radP (k := k)).map γ.toMonoidHom = KGL34P.radP :=
      map_mul_eq hαR (KGL34P.map_pow_eq_of_map_eq hβR j)
    rw [hγg, ← KGL34P.map_map_mulAut, ← KGL34P.map_map_mulAut, map_radP_fieldAut] at hγR
    apply radP_ne_map_alpha0 hk
    have h1 : (KGL34P.radP (k := k)).map α₀.toMonoidHom =
        (((KGL34P.radP (k := k)).map α₀.toMonoidHom).map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj g⁻¹).toMonoidHom := by
      rw [KGL34P.map_map_mulAut, ← map_mul, inv_mul_cancel, map_one]
      exact (Subgroup.map_id _).symm
    rw [hγR, map_conj_radP hk (inv_mem hgB)] at h1
    exact h1.symm
  rcases LinearThreeFourOuter.zmod_two_cases (Multiplicative.toAdd x) with hx | hx <;>
    rcases LinearThreeFourOuter.zmod_two_cases (Multiplicative.toAdd y) with hy | hy
  · exact absurd (by rw [hx, hy]; rfl) hw
  · exact graph hx hy
  · exact (field hx hy).elim
  · exact absurd (by rw [hx, hy]; rfl) hw

end L34G

theorem lieL34GraphMove_holds :
    ∀ (X : Type) [Group X] [Finite X], IsPSL 3 2 2 X →
      ∀ S : Subgroup X, IsSylowTwoOf S ⊤ → ∀ α β : MulAut X, (∃ k : ℕ, α ^ 2 ^ k = 1) →
        β ^ 3 = 1 → S.map α.toMonoidHom = S → S.map β.toMonoidHom = S → α * β * α⁻¹ = β⁻¹ →
        (∀ b ∈ Subgroup.normalizer (S : Set X), α b * b⁻¹ ∈ S) →
        (∀ b ∈ Subgroup.normalizer (S : Set X), β b * b⁻¹ ∈ S) →
        β ∉ (MulAut.conj : X →* MulAut X).range →
        ∃ Q : Subgroup X, Q ≤ S ∧ CFSG.Open.IsElemAbelian 2 Q ∧ Nat.card Q = 16 ∧
          Q.map α.toMonoidHom ≠ Q := by
  intro X _ _ hX S hS α β _ hβ3 hαS hβS hαβ hαB hβB hβ
  obtain ⟨k, _, hk, e, he⟩ := exists_mulEquiv_sylow_eq (Or.inl ⟨by decide, hX⟩) hS
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := MulAut.congr e with hc
  have hmemU : ∀ x : X, e x ∈ projUnitriangular 3 k ↔ x ∈ S := by
    intro x
    rw [← he, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hmemB : ∀ x : X, e x ∈ projUpperTriangular 3 k ↔
      x ∈ Subgroup.normalizer (S : Set X) := by
    intro x
    rw [← normalizer_projUnitriangular (n := 3) (K := k) 2, ← he,
      ← Subgroup.map_equiv_normalizer_eq, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hcapp : ∀ (γ : MulAut X) (x : X), c γ (e x) = e (γ x) := by
    intro γ x
    simp [hc, MulAut.congr_apply]
  have hB : ∀ γ : MulAut X, (∀ b ∈ Subgroup.normalizer (S : Set X), γ b * b⁻¹ ∈ S) →
      ∀ b ∈ projUpperTriangular 3 k, c γ b * b⁻¹ ∈ projUnitriangular 3 k := by
    intro γ hγ b hb
    obtain ⟨x, rfl⟩ := e.surjective b
    rw [hcapp, ← map_inv, ← map_mul, hmemU]
    exact hγ x ((hmemB x).mp hb)
  have key := L34G.map_radP_ne hk (α := c α) (β := c β) (by rw [← map_pow, hβ3, map_one])
    (by rw [← he, ← map_map_congr, hαS]) (by rw [← he, ← map_map_congr, hβS])
    (by rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, hαβ]) (hB α hαB) (hB β hβB)
    (by
      rintro ⟨y, hy⟩
      apply hβ
      refine ⟨e.symm y, c.injective ?_⟩
      rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, e.apply_symm_apply, hy])
  have hRe : ((KGL34P.radP (k := k)).map e.symm.toMonoidHom).map e.toMonoidHom =
      KGL34P.radP := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id (KGL34P.radP (k := k))
    ext y
    simp
  refine ⟨(KGL34P.radP (k := k)).map e.symm.toMonoidHom, ?_, ?_, ?_, fun h => key ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← hmemU]
    show e (e.symm y) ∈ _
    rw [e.apply_symm_apply]
    exact KGL34P.radP_le_projUnitriangular hy
  · exact isElemAbelian_map_mulEquiv e.symm
      ⟨⟨⟨fun x y => Subtype.ext (KGL34P.radP_comm x.2 y.2)⟩⟩, fun x hx => KGL34P.radP_sq hk hx⟩
  · rw [Subgroup.card_map_of_injective e.symm.injective, KGL34P.card_radP hk]
  · have h1 := map_map_congr e α ((KGL34P.radP (k := k)).map e.symm.toMonoidHom)
    rw [h, hRe] at h1
    exact h1.symm

end CFSG.Quasithin.H13.L32A.C
