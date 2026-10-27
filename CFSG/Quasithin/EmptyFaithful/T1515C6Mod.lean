module

public import CFSG.Quasithin.Background.Module
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin

section Dihedral

open DihedralGroup in
theorem dihedral3_gens {X : Type*} [Group X] {A : Subgroup X} (e : A ≃* DihedralGroup 3) :
    ∃ c t : X, c ∈ A ∧ t ∈ A ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ t * t = 1 ∧ t ≠ 1 ∧ t * c * t = c⁻¹ ∧
      ∀ a ∈ A, ∃ i j : ℕ, a = c ^ i * t ^ j := by
  have hr3 : (r 1 : DihedralGroup 3) ^ 3 = 1 := by decide
  have hss : (sr 0 : DihedralGroup 3) * sr 0 = 1 := by decide
  have hsrs : (sr 0 : DihedralGroup 3) * r 1 * sr 0 = (r 1)⁻¹ := by decide
  have hr1 : (r 1 : DihedralGroup 3) ≠ 1 := by decide
  have hs1 : (sr 0 : DihedralGroup 3) ≠ 1 := by decide
  have hnf : ∀ x : DihedralGroup 3, ∃ i : Fin 3, ∃ j : Fin 2,
      x = (r 1 : DihedralGroup 3) ^ (i : ℕ) * (sr 0) ^ (j : ℕ) := by decide
  set c : A := e.symm (r 1) with hc
  set t : A := e.symm (sr 0) with ht
  refine ⟨c, t, c.2, t.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : c ^ 3 = 1 := by rw [hc, ← map_pow, hr3, map_one]
    exact congrArg Subtype.val this
  · intro h
    have : c = 1 := Subtype.ext h
    exact hr1 (e.symm.injective (by rw [map_one]; exact this))
  · have : t * t = 1 := by rw [ht, ← map_mul, hss, map_one]
    exact congrArg Subtype.val this
  · intro h
    have : t = 1 := Subtype.ext h
    exact hs1 (e.symm.injective (by rw [map_one]; exact this))
  · have : t * c * t = c⁻¹ := by rw [ht, hc, ← map_mul, ← map_mul, hsrs, map_inv]
    exact congrArg Subtype.val this
  · intro a ha
    obtain ⟨i, j, hij⟩ := hnf (e ⟨a, ha⟩)
    refine ⟨i, j, ?_⟩
    have : (⟨a, ha⟩ : A) = c ^ (i : ℕ) * t ^ (j : ℕ) := by
      apply e.injective
      rw [hij, map_mul, map_pow, map_pow, hc, ht, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val this

end Dihedral


section DihedralPow

variable {X : Type*} [Group X]

theorem dihedral_t_pow {c t : X} (ht2 : t * t = 1) (htc : t * c * t = c⁻¹) (m : ℕ) :
    t * c ^ m * t = (c ^ m)⁻¹ := by
  induction m with
  | zero => simp [ht2]
  | succ n ih =>
    calc t * c ^ (n + 1) * t = (t * c ^ n * t) * (t * c * t) := by
          rw [pow_succ]
          calc t * (c ^ n * c) * t = t * c ^ n * (t * t) * c * t := by rw [ht2]; group
            _ = (t * c ^ n * t) * (t * c * t) := by group
      _ = (c ^ n)⁻¹ * c⁻¹ := by rw [ih, htc]
      _ = (c ^ (n + 1))⁻¹ := by rw [pow_succ', mul_inv_rev]

theorem pow_odd_of_sq_eq_one {s : X} (hs : s * s = 1) {k : ℕ} (hk : Odd k) : s ^ k = s := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul, pow_two, hs, one_pow, one_mul]

theorem pow_eq_one_or_self {t : X} (ht2 : t * t = 1) (j : ℕ) : t ^ j = 1 ∨ t ^ j = t := by
  induction j with
  | zero => left; simp
  | succ n ih =>
    rcases ih with h | h
    · right; rw [pow_succ, h, one_mul]
    · left; rw [pow_succ, h, ht2]


theorem dihedral_refl_sq {c t : X} (ht2 : t * t = 1) (htc : t * c * t = c⁻¹) (i : ℕ) :
    (c ^ i * t) * (c ^ i * t) = 1 := by
  calc (c ^ i * t) * (c ^ i * t) = c ^ i * (t * c ^ i * t) := by group
    _ = 1 := by rw [dihedral_t_pow ht2 htc, mul_inv_cancel]

end DihedralPow

section Module

variable {V : Type*} [CommGroup V]

private theorem dihedral_apply_rels {c t : MulAut V} (hc3 : c ^ 3 = 1) (ht2 : t * t = 1)
    (htc : t * c * t = c⁻¹) :
    (∀ v : V, c (c (c v)) = v) ∧ (∀ v : V, t (t v) = v) ∧
      (∀ v : V, t (c v) = c (c (t v))) ∧ (∀ v : V, c (t v) = t (c (c v))) := by
  have h3 : c * (c * c) = 1 := by
    have : c ^ 3 = c * (c * c) := by rw [pow_succ, pow_succ, pow_one, mul_assoc]
    rwa [this] at hc3
  have hcinv : c⁻¹ = c * c := by
    refine inv_eq_of_mul_eq_one_right ?_
    exact h3
  have htc' : t * c = c * c * t := by
    have : t * c * t * t = c⁻¹ * t := by rw [htc]
    rw [mul_assoc, ht2, mul_one, hcinv] at this
    exact this
  have hct' : c * t = t * (c * c) := by
    calc c * t = (t * t) * c * t := by rw [ht2, one_mul]
      _ = t * (t * c) * t := by group
      _ = t * (c * c * t) * t := by rw [htc']
      _ = t * (c * c) * (t * t) := by group
      _ = t * (c * c) := by rw [ht2, mul_one]
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · exact congrArg (fun φ : MulAut V => φ v) h3
  · exact congrArg (fun φ : MulAut V => φ v) ht2
  · exact congrArg (fun φ : MulAut V => φ v) htc'
  · exact congrArg (fun φ : MulAut V => φ v) hct'

private def normC (c : MulAut V) : V →* V where
  toFun v := v * c v * c (c v)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    ac_rfl

private def comT (t : MulAut V) : V →* V where
  toFun v := t v * v⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv]
    ac_rfl

private theorem comT_comT (hsq : ∀ v : V, v * v = 1) {t : MulAut V} (ht2 : t * t = 1) (v : V) :
    comT t (comT t v) = 1 := by
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  have htt : ∀ v : V, t (t v) = v := fun v => congrArg (fun φ : MulAut V => φ v) ht2
  have h1 : comT t v = t v * v := by
    show t v * v⁻¹ = t v * v
    rw [hinv v]
  have h2 : t (comT t v) = comT t v := by
    rw [h1, map_mul, htt, mul_comm]
  show t (comT t v) * (comT t v)⁻¹ = 1
  rw [h2]
  exact mul_inv_cancel _

theorem fix_eq_one_of_dihedral3 (hsq : ∀ v : V, v * v = 1) {c t : MulAut V} (hc3 : c ^ 3 = 1)
    (ht2 : t * t = 1) (htc : t * c * t = c⁻¹) {A : Subgroup (MulAut V)}
    (hA : ∀ a ∈ A, ∃ i j : ℕ, a = c ^ i * t ^ j) {W : Subgroup V}
    (hWA : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W)
    (hcA : c ∈ A)
    (hgen : W ≤ Subgroup.closure {x : V | ∃ a ∈ A, ∃ w ∈ W, x = a w * w⁻¹}) :
    ∀ w ∈ W, c w = w → w = 1 := by
  obtain ⟨hc3', htt, htc1, hct1⟩ := dihedral_apply_rels hc3 ht2 htc
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  set f : V →* V := normC c with hf
  have hfv : ∀ v : V, f v = v * c v * c (c v) := fun v => rfl
  have hcf : ∀ v : V, c (f v) = f v := by
    intro v
    rw [hfv, map_mul, map_mul, hc3']
    ac_rfl
  have hfc : ∀ v : V, f (c v) = f v := by
    intro v
    rw [hfv, hfv, hc3']
    ac_rfl
  have hct : ∀ v : V, c (c (c (c v))) = c v := fun v => by rw [hc3']
  have hft : ∀ v : V, f (t v) = t (f v) := by
    intro v
    have e1 : c (t v) = t (c (c v)) := hct1 v
    have e2 : c (c (t v)) = t (c v) := by
      rw [e1, hct1 (c (c v)), hct v]
    rw [hfv, hfv, e2, e1, map_mul, map_mul]
    ac_rfl
  have hP : ∀ φ : MulAut V, (∀ v, f (φ v) = φ (f v)) → ∀ ψ : MulAut V,
      (∀ v, f (ψ v) = ψ (f v)) → ∀ v, f ((φ * ψ) v) = (φ * ψ) (f v) := by
    intro φ hφ ψ hψ v
    show f (φ (ψ v)) = φ (ψ (f v))
    rw [hφ, hψ]
  have hPc : ∀ v, f (c v) = c (f v) := fun v => by rw [hfc, hcf]
  have hPcpow : ∀ i : ℕ, ∀ v, f ((c ^ i) v) = (c ^ i) (f v) := by
    intro i
    induction i with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ]
      exact hP _ ih _ hPc v
  have hPtpow : ∀ j : ℕ, ∀ v, f ((t ^ j) v) = (t ^ j) (f v) := by
    intro j
    induction j with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ]
      exact hP _ ih _ hft v
  have hPA : ∀ a ∈ A, ∀ v, f (a v) = a (f v) := by
    intro a ha v
    obtain ⟨i, j, rfl⟩ := hA a ha
    exact hP (c ^ i) (hPcpow i) (t ^ j) (hPtpow j) v
  have hfW : ∀ w ∈ W, f w ∈ W := by
    intro w hw
    have h1 : c w ∈ W := hWA c hcA w hw
    have h2 : c (c w) ∈ W := hWA c hcA _ h1
    rw [hfv]
    exact W.mul_mem (W.mul_mem hw h1) h2
  set W₀ : Subgroup V := W ⊓ MonoidHom.eqLocus c.toMonoidHom (MonoidHom.id V) with hW₀
  have hW₀mem : ∀ x : V, x ∈ W₀ ↔ x ∈ W ∧ c x = x := by
    intro x
    rw [hW₀, Subgroup.mem_inf]
    exact Iff.rfl
  have hpowt : ∀ j : ℕ, t ^ j = 1 ∨ t ^ j = t := by
    intro j
    induction j with
    | zero => left; simp
    | succ n ih =>
      rcases ih with h | h
      · right; rw [pow_succ, h, one_mul]
      · left; rw [pow_succ, h, ht2]
  have hpowc : ∀ i : ℕ, ∀ u : V, c u = u → (c ^ i) u = u := by
    intro i
    induction i with
    | zero => intro u _; simp
    | succ n ih =>
      intro u hu
      rw [pow_succ]
      show (c ^ n) (c u) = u
      rw [hu]
      exact ih u hu
  have hctfix : ∀ u : V, c u = u → c (t u) = t u := by
    intro u hu
    rw [hct1, hu, hu]
  have key : ∀ u ∈ W, c u = u → ∃ x ∈ W, c x = x ∧ comT t x = u := by
    intro u huW huc
    have hfu : f u = u := by
      rw [hfv, huc, huc]
      calc u * u * u = (u * u) * u := rfl
        _ = u := by rw [hsq u, one_mul]
    have hu : u ∈ Subgroup.closure {x : V | ∃ a ∈ A, ∃ w ∈ W, x = a w * w⁻¹} := hgen huW
    have hmem : f u ∈ (Subgroup.closure {x : V | ∃ a ∈ A, ∃ w ∈ W, x = a w * w⁻¹}).map f :=
      Subgroup.mem_map_of_mem f hu
    rw [MonoidHom.map_closure] at hmem
    have hle : Subgroup.closure (f '' {x : V | ∃ a ∈ A, ∃ w ∈ W, x = a w * w⁻¹}) ≤
        W₀.map (comT t) := by
      rw [Subgroup.closure_le]
      rintro y ⟨x, ⟨a, ha, w, hw, rfl⟩, rfl⟩
      have hu'W : f w ∈ W := hfW w hw
      have hu'c : c (f w) = f w := hcf w
      have hy : f (a w * w⁻¹) = a (f w) * (f w)⁻¹ := by
        rw [map_mul, map_inv, hPA a ha]
      rw [SetLike.mem_coe, hy]
      obtain ⟨i, j, rfl⟩ := hA a ha
      have hav : (c ^ i * t ^ j) (f w) = f w ∨ (c ^ i * t ^ j) (f w) = t (f w) := by
        show (c ^ i) ((t ^ j) (f w)) = f w ∨ (c ^ i) ((t ^ j) (f w)) = t (f w)
        rcases hpowt j with h | h
        · left
          rw [h]
          exact hpowc i _ hu'c
        · right
          rw [h]
          exact hpowc i _ (hctfix _ hu'c)
      rcases hav with h | h
      · rw [h, mul_inv_cancel]
        exact (W₀.map (comT t)).one_mem
      · rw [h]
        exact ⟨f w, (hW₀mem _).mpr ⟨hu'W, hu'c⟩, rfl⟩
    have := hle hmem
    rw [hfu] at this
    obtain ⟨x, hx, hxu⟩ := this
    exact ⟨x, ((hW₀mem x).mp hx).1, ((hW₀mem x).mp hx).2, hxu⟩
  intro w₀ hw₀ hcw₀
  obtain ⟨x, hxW, hxc, hxw⟩ := key w₀ hw₀ hcw₀
  obtain ⟨x', hx'W, hx'c, hx'x⟩ := key x hxW hxc
  rw [← hxw, ← hx'x]
  exact comT_comT hsq ht2 x'

private theorem t_comT (hsq : ∀ v : V, v * v = 1) {t : MulAut V} (ht2 : t * t = 1) (v : V) :
    t (comT t v) = comT t v := by
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  have htt : ∀ v : V, t (t v) = v := fun v => congrArg (fun φ : MulAut V => φ v) ht2
  have h1 : comT t v = t v * v := by
    show t v * v⁻¹ = t v * v
    rw [hinv v]
  rw [h1, map_mul, htt, mul_comm]

theorem card_fix_t_of_dihedral3 (hsq : ∀ v : V, v * v = 1) {c t : MulAut V} (hc3 : c ^ 3 = 1)
    (ht2 : t * t = 1) (htc : t * c * t = c⁻¹) {A : Subgroup (MulAut V)}
    (hA : ∀ a ∈ A, ∃ i j : ℕ, a = c ^ i * t ^ j) {W : Subgroup V}
    (hWA : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) (hcA : c ∈ A) (htA : t ∈ A)
    (hgen : W ≤ Subgroup.closure {x : V | ∃ a ∈ A, ∃ w ∈ W, x = a w * w⁻¹})
    (hW16 : Nat.card W = 16) :
    Nat.card (W ⊓ MonoidHom.eqLocus t.toMonoidHom (MonoidHom.id V) : Subgroup V) = 4 := by
  have hfix := fix_eq_one_of_dihedral3 hsq hc3 ht2 htc hA hWA hcA hgen
  obtain ⟨hc3', htt, htc1, hct1⟩ := dihedral_apply_rels hc3 ht2 htc
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_right (hsq v)
  set F : Subgroup V := W ⊓ MonoidHom.eqLocus t.toMonoidHom (MonoidHom.id V) with hF
  have hFmem : ∀ x : V, x ∈ F ↔ x ∈ W ∧ t x = x := by
    intro x
    rw [hF, Subgroup.mem_inf]
    exact Iff.rfl
  have hcW : ∀ w ∈ W, c w ∈ W := fun w hw => hWA c hcA w hw
  have htW : ∀ w ∈ W, t w ∈ W := fun w hw => hWA t htA w hw
  have hct4 : ∀ v : V, c (c (c (c v))) = c v := fun v => by rw [hc3']
  have hnorm : ∀ w ∈ W, w * c w * c (c w) = 1 := by
    intro w hw
    refine hfix _ (W.mul_mem (W.mul_mem hw (hcW w hw)) (hcW _ (hcW w hw))) ?_
    rw [map_mul, map_mul, hc3']
    ac_rfl
  let φ : F × F →* V :=
    (F.subtype).coprod (((c * c).toMonoidHom).comp F.subtype)
  have hφ : ∀ x y : F, φ (x, y) = (x : V) * c (c (y : V)) := fun x y => rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    rintro ⟨x, y⟩ hxy
    rw [MonoidHom.mem_ker, hφ] at hxy
    have hx : (x : V) = c (c (y : V)) := by
      have : (x : V) = (c (c (y : V)))⁻¹ := eq_inv_of_mul_eq_one_left hxy
      rw [this, ← map_inv, ← map_inv, hinv]
    have hyW := ((hFmem _).mp y.2)
    have hxt := ((hFmem _).mp x.2).2
    have hty := hyW.2
    have h1 : t (c (c (y : V))) = c (y : V) := by
      rw [htc1 (c (y : V)), htc1 (y : V), hty, hct4]
    have h2 : c (y : V) = c (c (y : V)) := by
      calc c (y : V) = t (c (c (y : V))) := h1.symm
        _ = t (x : V) := by rw [← hx]
        _ = (x : V) := hxt
        _ = c (c (y : V)) := hx
    have h3 : (y : V) = c (y : V) := c.injective h2
    have h4 : (y : V) = 1 := hfix _ hyW.1 h3.symm
    have h5 : (x : V) = 1 := by rw [hx, h4, map_one, map_one]
    exact Prod.ext (Subtype.ext h5) (Subtype.ext h4)
  have hmemF : ∀ v ∈ W, comT t v ∈ F := fun v hv =>
    (hFmem _).mpr ⟨W.mul_mem (htW v hv) (W.inv_mem hv), t_comT hsq ht2 v⟩
  have hrange : φ.range = W := by
    apply le_antisymm
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      rw [hφ]
      exact W.mul_mem ((hFmem _).mp x.2).1 (hcW _ (hcW _ ((hFmem _).mp y.2).1))
    · intro w hw
      have e1 : comT t (c w) = c (c (t w)) * c w := by
        show t (c w) * (c w)⁻¹ = _
        rw [htc1, hinv]
      have e2 : c (c (comT t w)) = c (c (t w)) * c (c w) := by
        show c (c (t w * w⁻¹)) = _
        rw [hinv, map_mul, map_mul]
      have hbd : c w * c (c w) = w := by
        have h := hnorm w hw
        rw [mul_assoc] at h
        have := eq_inv_of_mul_eq_one_right h
        rw [this, hinv]
      have hsqc : c (c (t w)) * c (c (t w)) = 1 := hsq _
      refine ⟨(⟨comT t (c w), hmemF _ (hcW w hw)⟩, ⟨comT t w, hmemF _ hw⟩), ?_⟩
      rw [hφ]
      show comT t (c w) * c (c (comT t w)) = w
      rw [e1, e2]
      calc c (c (t w)) * c w * (c (c (t w)) * c (c w))
          = (c (c (t w)) * c (c (t w))) * (c w * c (c w)) := by ac_rfl
        _ = w := by rw [hsqc, one_mul, hbd]
  have hcardW : Nat.card W = Nat.card F * Nat.card F := by
    have h1 : Nat.card (F × F) = Nat.card φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have h2 : Nat.card φ.range = Nat.card W :=
      Nat.card_congr (MulEquiv.subgroupCongr hrange).toEquiv
    rw [← h2, ← h1, Nat.card_prod]
  rw [hW16] at hcardW
  have h44 : Nat.card F * Nat.card F = 4 * 4 := by omega
  exact Nat.mul_self_inj.mp h44

theorem card_fix_involution_of_dihedral3 (hsq : ∀ v : V, v * v = 1) {c t : MulAut V}
    (hc3 : c ^ 3 = 1) (ht2 : t * t = 1) (htc : t * c * t = c⁻¹) {A : Subgroup (MulAut V)}
    (hA : ∀ a ∈ A, ∃ i j : ℕ, a = c ^ i * t ^ j) {W : Subgroup V}
    (hWA : ∀ a ∈ A, ∀ w ∈ W, a w ∈ W) (hcA : c ∈ A) (htA : t ∈ A)
    (hgen : W ≤ Subgroup.closure {x : V | ∃ a ∈ A, ∃ w ∈ W, x = a w * w⁻¹})
    (hW16 : Nat.card W = 16) {s : MulAut V} (hsA : s ∈ A) (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    Nat.card (W ⊓ MonoidHom.eqLocus s.toMonoidHom (MonoidHom.id V) : Subgroup V) = 4 := by
  have h4 := card_fix_t_of_dihedral3 hsq hc3 ht2 htc hA hWA hcA htA hgen hW16
  obtain ⟨i, j, hij⟩ := hA s hsA
  have hpowt : ∀ j : ℕ, t ^ j = 1 ∨ t ^ j = t := by
    intro j
    induction j with
    | zero => left; simp
    | succ n ih =>
      rcases ih with h | h
      · right; rw [pow_succ, h, one_mul]
      · left; rw [pow_succ, h, ht2]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htcm : ∀ m : ℕ, t * c ^ m * t = (c ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => simp [ht2]
    | succ n ih =>
      calc t * c ^ (n + 1) * t = (t * c ^ n * t) * (t * c * t) := by
            rw [pow_succ]
            calc t * (c ^ n * c) * t = t * c ^ n * (t * t) * c * t := by rw [ht2]; group
              _ = (t * c ^ n * t) * (t * c * t) := by group
        _ = (c ^ n)⁻¹ * c⁻¹ := by rw [ih, htc]
        _ = (c ^ (n + 1))⁻¹ := by rw [pow_succ', mul_inv_rev]
  have hs : s = c ^ i * t := by
    rcases hpowt j with hj | hj
    · exfalso
      rw [hj, mul_one] at hij
      apply hs1
      have h3 : s ^ 3 = 1 := by rw [hij, ← pow_mul, mul_comm, pow_mul, hc3, one_pow]
      have h2 : s ^ 2 = 1 := by rw [pow_two]; exact hs2
      have : s ^ 3 = s ^ 2 * s := by rw [pow_succ]
      rw [h2, one_mul] at this
      rw [← this]
      exact h3
    · rw [hj] at hij
      exact hij
  set g : MulAut V := c ^ (2 * i) with hg
  have hgA : g ∈ A := A.pow_mem hcA _
  have hgtg : g * t * g⁻¹ = s := by
    have h1 : t * g⁻¹ = g * t := by
      have := htcm (2 * i)
      calc t * g⁻¹ = t * g⁻¹ * (t * t) := by rw [ht2, mul_one]
        _ = (t * g * t)⁻¹ * t := by rw [mul_inv_rev, mul_inv_rev, htinv]; group
        _ = g * t := by rw [hg, this, inv_inv]
    have h2 : g * g = c ^ i := by
      rw [hg, ← pow_add]
      have : 2 * i + 2 * i = i + 3 * i := by ring
      rw [this, pow_add, pow_mul, hc3, one_pow, mul_one]
    calc g * t * g⁻¹ = g * (t * g⁻¹) := by group
      _ = g * (g * t) := by rw [h1]
      _ = (g * g) * t := by group
      _ = s := by rw [h2, hs]
  have hgW : ∀ w ∈ W, g w ∈ W := fun w hw => hWA g hgA w hw
  have hgiW : ∀ w ∈ W, g⁻¹ w ∈ W := fun w hw => hWA g⁻¹ (A.inv_mem hgA) w hw
  rw [← h4]
  refine Nat.card_congr
    { toFun := fun w => ⟨g⁻¹ w, ?_, ?_⟩
      invFun := fun w => ⟨g w, ?_, ?_⟩
      left_inv := fun w => ?_
      right_inv := fun w => ?_ }
  · exact hgiW w.1 (Subgroup.mem_inf.mp w.2).1
  · have hw : s.toMonoidHom w.1 = (MonoidHom.id V) w.1 := (Subgroup.mem_inf.mp w.2).2
    show t (g⁻¹ w.1) = g⁻¹ w.1
    have h1 : s w.1 = w.1 := hw
    have h2 : (g * t * g⁻¹) w.1 = w.1 := by rw [hgtg]; exact h1
    have h3 : g (t (g⁻¹ w.1)) = w.1 := h2
    calc t (g⁻¹ w.1) = g⁻¹ (g (t (g⁻¹ w.1))) := by simp
      _ = g⁻¹ w.1 := by rw [h3]
  · exact hgW w.1 (Subgroup.mem_inf.mp w.2).1
  · have hw : t.toMonoidHom w.1 = (MonoidHom.id V) w.1 := (Subgroup.mem_inf.mp w.2).2
    show s (g w.1) = g w.1
    have h1 : t w.1 = w.1 := hw
    rw [← hgtg]
    show g (t (g⁻¹ (g w.1))) = g w.1
    simp [h1]
  · apply Subtype.ext
    show g (g⁻¹ w.1) = w.1
    simp
  · apply Subtype.ext
    show g⁻¹ (g w.1) = w.1
    simp

end Module

end CFSG.Quasithin
