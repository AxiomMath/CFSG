module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.LieType.BorelTits.Families

public section

namespace CFSG.RankThree.OrthogonalInvolutions

open Module QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem map_add_smul_add_smul (Q : QuadraticForm K V) (v w z : V) (a b : K) :
    Q (v + a • w + b • z) = Q v + a * a * Q w + b * b * Q z + a * polar Q v w +
      b * polar Q v z + a * b * polar Q w z := by
  simp only [map_add_eq, QuadraticMap.map_smul, polar_add_left, polar_smul_left, polar_smul_right,
    smul_eq_mul]
  ring

theorem injective_of_map_eq {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate)
    {g : V →ₗ[K] V} (hg : ∀ v, Q (g v) = Q v) : Function.Injective g :=
  (toQuadForm Q hQ).injective_of_Q hg

theorem exists_polar_ne_zero [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {U₀ : Submodule K V} {v : V} (hv : v ∉ U₀) :
    ∃ z, (∀ x ∈ U₀, polar Q x z = 0) ∧ polar Q v z ≠ 0 := by
  by_contra! h
  apply hv
  rw [← (toQuadForm Q hQ).polar.perp_perp U₀, CFSG.LieType.BorelTits.ReflForm.mem_perp]
  intro z hz
  rw [CFSG.LieType.BorelTits.ReflForm.mem_perp] at hz
  rw [toQuadForm_polar_β, polar_comm]
  exact h z hz

theorem exists_polar_ne_zero_ne_zero [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {U₀ : Submodule K V} {u u' : V} (hu : u ∉ U₀)
    (hu' : u' ∉ U₀) :
    ∃ z, (∀ x ∈ U₀, polar Q x z = 0) ∧ polar Q u z ≠ 0 ∧ polar Q u' z ≠ 0 := by
  obtain ⟨z₁, hz₁, h₁⟩ := exists_polar_ne_zero hQ hu
  obtain ⟨z₂, hz₂, h₂⟩ := exists_polar_ne_zero hQ hu'
  by_cases h12 : polar Q u' z₁ = 0
  · by_cases h21 : polar Q u z₂ = 0
    · refine ⟨z₁ + z₂, fun x hx => ?_, ?_, ?_⟩
      · rw [polar_add_right, hz₁ x hx, hz₂ x hx, add_zero]
      · rw [polar_add_right, h21, add_zero]
        exact h₁
      · rw [polar_add_right, h12, zero_add]
        exact h₂
    · exact ⟨z₂, hz₂, h21, h₂⟩
  · exact ⟨z₁, hz₁, h₁, h12⟩

section CharTwo

variable [CharP K 2]

theorem exists_mem_orthogonalGroup_fix_apply_eq [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {U₀ : Submodule K V} {u u' : V} (hu : u ∉ U₀)
    (hu' : u' ∉ U₀) (hQu : Q u' = Q u) (hpol : ∀ x ∈ U₀, polar Q u' x = polar Q u x) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, (∀ x ∈ U₀, g x = x) ∧ g u = u' := by
  set w := u' - u with hw
  have hwU : ∀ x ∈ U₀, polar Q w x = 0 := fun x hx => by
    rw [hw, QuadraticMap.polar_sub_left, hpol x hx, sub_self]
  have hQw : Q w = polar Q u' u := by
    rw [hw, sub_eq_add_vec K, map_add_eq, hQu, CharTwo.add_self_eq_zero, zero_add]
  have hpwu : polar Q w u = Q w := by
    rw [hQw, hw, QuadraticMap.polar_sub_left, polar_self_eq_zero, sub_zero]
  by_cases h0 : Q w = 0
  ·
    obtain ⟨z, hzU, hz1, hz2⟩ := exists_polar_ne_zero_ne_zero hQ hu hu'
    set c := polar Q u' z with hc
    set d := polar Q u z with hd
    let ℓw : V →ₗ[K] K := (Q.polarBilin).flip w
    let ℓz : V →ₗ[K] K := (Q.polarBilin).flip z
    have hℓw : ∀ v, ℓw v = polar Q v w := fun v => rfl
    have hℓz : ∀ v, ℓz v = polar Q v z := fun v => rfl
    let β : V →ₗ[K] K := c⁻¹ • ℓw
    let α : V →ₗ[K] K := d⁻¹ • (ℓz - (Q z * c⁻¹) • ℓw)
    let G : V →ₗ[K] V := LinearMap.id + α.smulRight w + β.smulRight z
    have hG : ∀ v, G v = v + α v • w + β v • z := fun v => rfl
    have hβ : ∀ v, polar Q v w = β v * c := fun v => by
      change _ = c⁻¹ * ℓw v * c
      rw [hℓw, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hz2, mul_one]
    have hα : ∀ v, polar Q v z = α v * d + β v * Q z := fun v => by
      change _ = d⁻¹ * (ℓz v - Q z * c⁻¹ * ℓw v) * d + c⁻¹ * ℓw v * Q z
      rw [hℓz, hℓw]
      field_simp
      ring
    have hwz : polar Q w z = c - d := by rw [hw, QuadraticMap.polar_sub_left]
    have hGQ : ∀ v, Q (G v) = Q v := fun v => by
      rw [hG, map_add_smul_add_smul, h0, hβ v, hα v, hwz]
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      linear_combination (β v * β v * Q z + α v * β v * c) * h2
    have hinj := injective_of_map_eq hQ hGQ
    refine ⟨LinearEquiv.ofInjectiveEndo G hinj,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => hGQ v, fun x hx => ?_, ?_⟩
    · change G x = x
      have hxw : polar Q x w = 0 := by rw [polar_comm]; exact hwU x hx
      have hb : β x = 0 := by
        change c⁻¹ * ℓw x = 0
        rw [hℓw, hxw, mul_zero]
      have ha : α x = 0 := by
        change d⁻¹ * (ℓz x - Q z * c⁻¹ * ℓw x) = 0
        rw [hℓz, hℓw, hzU x hx, hxw, mul_zero, sub_zero, mul_zero]
      rw [hG, ha, hb, zero_smul, zero_smul, add_zero, add_zero]
    · change G u = u'
      have huw : polar Q u w = 0 := by rw [polar_comm, hpwu, h0]
      have hb : β u = 0 := by
        change c⁻¹ * ℓw u = 0
        rw [hℓw, huw, mul_zero]
      have ha : α u = 1 := by
        change d⁻¹ * (ℓz u - Q z * c⁻¹ * ℓw u) = 1
        rw [hℓz, hℓw, huw, mul_zero, sub_zero, ← hd, inv_mul_cancel₀ hz1]
      rw [hG, ha, hb, one_smul, zero_smul, add_zero, hw, add_sub_cancel]
  ·
    let _ : Invertible (Q w) := invertibleOfNonzero h0
    refine ⟨TauCeti.QuadraticMap.reflection Q w,
      TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q w, fun x hx => ?_, ?_⟩
    · rw [TauCeti.QuadraticMap.reflection_apply, hwU x hx, mul_zero, zero_smul, sub_zero]
    · rw [TauCeti.QuadraticMap.reflection_apply, hpwu, invOf_mul_self, one_smul, hw,
        sub_eq_add_vec K u' u, sub_eq_add_vec K, add_left_comm, add_self_vec K, add_zero]

theorem exists_mem_orthogonalGroup_apply_eq [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) :
    ∀ {k : ℕ} (u u' : Fin k → V), LinearIndependent K u → LinearIndependent K u' →
      (∀ i, Q (u' i) = Q (u i)) → (∀ i j, polar Q (u' i) (u' j) = polar Q (u i) (u j)) →
      ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ i, g (u i) = u' i := by
  intro k
  induction k with
  | zero => exact fun _ _ _ _ _ _ => ⟨1, one_mem _, fun i => i.elim0⟩
  | succ k ih =>
    intro u u' hu hu' hQu hpol
    rw [linearIndependent_finSucc'] at hu hu'
    obtain ⟨h, hhO, hh⟩ := ih (Fin.init u) (Fin.init u') hu.1 hu'.1 (fun i => hQu _)
      (fun i j => hpol _ _)
    have hh' : ∀ i : Fin k, h (u (Fin.castSucc i)) = u' (Fin.castSucc i) := fun i => hh i
    set U₀ := Submodule.span K (Set.range (Fin.init u)) with hU₀
    set x' := h⁻¹ (u' (Fin.last k)) with hx'
    have hinvO : h⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := inv_mem hhO
    have hinv : ∀ i, h⁻¹ (u' (Fin.castSucc i)) = u (Fin.castSucc i) := fun i => by
      rw [← hh' i, ← LinearEquiv.mul_apply, inv_mul_cancel, LinearEquiv.coe_one, id]
    have hx'U : x' ∉ U₀ := by
      intro hmem
      apply hu'.2
      have hmap : U₀.map (h : V →ₗ[K] V) = Submodule.span K (Set.range (Fin.init u')) := by
        rw [hU₀, Submodule.map_span, ← Set.range_comp]
        have hcomp : (⇑(h : V →ₗ[K] V) ∘ Fin.init u) = Fin.init u' := funext hh
        rw [hcomp]
      rw [← hmap]
      refine ⟨x', hmem, ?_⟩
      change h (h⁻¹ (u' (Fin.last k))) = u' (Fin.last k)
      rw [← LinearEquiv.mul_apply, mul_inv_cancel, LinearEquiv.coe_one, id]
    have hQx' : Q x' = Q (u (Fin.last k)) := by
      rw [hx', TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hinvO, hQu]
    have hpolx' : ∀ y ∈ U₀, polar Q x' y = polar Q (u (Fin.last k)) y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        change polar Q x' (u (Fin.castSucc i)) = polar Q (u (Fin.last k)) (u (Fin.castSucc i))
        conv_lhs => rw [← hinv i]
        rw [hx', TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hinvO, hpol]
      | zero => rw [polar_zero_right, polar_zero_right]
      | add y y' _ _ h1 h2 => rw [polar_add_right, polar_add_right, h1, h2]
      | smul a y _ h1 => rw [polar_smul_right, polar_smul_right, h1]
    obtain ⟨g', hg'O, hg'fix, hg'u⟩ :=
      exists_mem_orthogonalGroup_fix_apply_eq hQ hu.2 hx'U hQx' hpolx'
    refine ⟨h * g', mul_mem hhO hg'O, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [LinearEquiv.mul_apply, hg'u, hx', ← LinearEquiv.mul_apply, mul_inv_cancel,
        LinearEquiv.coe_one, id]
    · rw [LinearEquiv.mul_apply, hg'fix (u (Fin.castSucc i)) (Submodule.subset_span ⟨i, rfl⟩)]
      exact hh' i

end CharTwo

end CFSG.RankThree.OrthogonalInvolutions
