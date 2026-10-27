module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem add_self_eq_zero' {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  have h : ((1 : ZMod 2) + 1) • x = 0 := by
    have h1 : (1 : ZMod 2) + 1 = 0 := by decide
    rw [h1, zero_smul]
  rwa [add_smul, one_smul] at h

theorem neg_eq_self' {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (x : M) : -x = x :=
  neg_eq_of_add_eq_zero_right (add_self_eq_zero' x)

theorem bil_comm_of_alt {B : LinearMap.BilinForm (ZMod 2) W} (hAlt : B.IsAlt) (x y : W) :
    B x y = B y x := by
  have h := hAlt.neg_eq x y
  have h2 : ∀ t : ZMod 2, -t = t := by decide
  rw [h2] at h
  exact h

theorem plane_mem_cases {P : Submodule (ZMod 2) W} (hP : Module.finrank (ZMod 2) P = 2)
    {p v : W} (hp : p ∈ P) (hv : v ∈ P) (hp0 : p ≠ 0) (hv0 : v ≠ 0) (hvp : v ≠ p) :
    ∀ x ∈ P, x = 0 ∨ x = p ∨ x = v ∨ x = p + v := by
  have hfin : Module.Finite (ZMod 2) P :=
    Module.finite_of_finrank_pos (by rw [hP]; norm_num)
  have hs : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have hli : LinearIndependent (ZMod 2) ![p, v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases hs s with rfl | rfl <;> rcases hs t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · simp at hst; exact absurd hst hv0
    · simp at hst; exact absurd hst hp0
    · simp at hst
      exact absurd (by rw [eq_neg_of_add_eq_zero_right hst, neg_eq_self']) hvp
  have hle : Submodule.span (ZMod 2) {p, v} ≤ P := by
    rw [Submodule.span_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact hp
    · exact hv
  have hrange : Set.range ![p, v] = {p, v} := by
    ext x; simp [Fin.exists_fin_two]; tauto
  have hfr : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {p, v}) = 2 := by
    have := finrank_span_eq_card hli
    rw [hrange] at this
    simpa using this
  have hspan : Submodule.span (ZMod 2) {p, v} = P :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hP])
  intro x hx
  rw [← hspan, Submodule.mem_span_pair] at hx
  obtain ⟨s, t, rfl⟩ := hx
  rcases hs s with rfl | rfl <;> rcases hs t with rfl | rfl <;> simp

theorem plane_pairing_one {B : LinearMap.BilinForm (ZMod 2) W} (hAlt : B.IsAlt)
    {P : Submodule (ZMod 2) W} (hP : Module.finrank (ZMod 2) P = 2)
    (hnd : P ⊓ B.orthogonal P = ⊥) {u v : W} (hu : u ∈ P) (hv : v ∈ P)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) : B u v = 1 := by
  have hcases := plane_mem_cases hP hu hv hu0 hv0 huv.symm
  by_contra h
  have h0 : B u v = 0 := by
    have : ∀ t : ZMod 2, t ≠ 1 → t = 0 := by decide
    exact this _ h
  have hmem : u ∈ P ⊓ B.orthogonal P := by
    refine Submodule.mem_inf.mpr ⟨hu, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    rcases hcases x hx with rfl | rfl | rfl | rfl
    · simp
    · exact hAlt.self_eq_zero _
    · rw [bil_comm_of_alt hAlt]; exact h0
    · rw [map_add, LinearMap.add_apply, hAlt.self_eq_zero, zero_add, bil_comm_of_alt hAlt]
      exact h0
  rw [hnd, Submodule.mem_bot] at hmem
  exact hu0 hmem

theorem matrix_two_order_three (A M : Matrix (Fin 2) (Fin 2) (ZMod 2)) (hA : A ^ 2 + A + 1 = 0)
    (hM : M ^ 3 = 1) : M = 1 ∨ M = A ∨ M = A ^ 2 := by
  revert A M
  decide

theorem endo_two_order_three {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (h2 : Module.finrank (ZMod 2) V = 2) {T M : V →ₗ[ZMod 2] V}
    (hT : T ^ 2 + T + 1 = 0) (hM : M ^ 3 = 1) : M = 1 ∨ M = T ∨ M = T ^ 2 := by
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  let b := Module.finBasisOfFinrankEq (ZMod 2) V h2
  let ψ := LinearMap.toMatrixAlgEquiv b
  have hA : (ψ T) ^ 2 + ψ T + 1 = 0 := by
    have : ψ (T ^ 2 + T + 1) = 0 := by rw [hT, map_zero]
    simpa [map_add, map_pow, map_one] using this
  have hM' : (ψ M) ^ 3 = 1 := by
    have : ψ (M ^ 3) = 1 := by rw [hM, map_one]
    simpa [map_pow] using this
  rcases matrix_two_order_three (ψ T) (ψ M) hA hM' with h | h | h
  · left; exact ψ.injective (by rw [h, map_one])
  · right; left; exact ψ.injective h
  · right; right; exact ψ.injective (by rw [h, map_pow])

theorem pow_four_eq_one_of_sub_one_cube {R : Type*} [Ring R] (h2 : (2 : R) = 0) {y : R}
    (h : (y - 1) ^ 3 = 0) : y ^ 4 = 1 := by
  have hsq : ∀ x : R, (x + 1) ^ 2 = x ^ 2 + 1 := by
    intro x
    have : (x + 1) ^ 2 = x ^ 2 + 1 + 2 * x := by noncomm_ring
    rw [this, h2, zero_mul, add_zero]
  have h4 : (y - 1) ^ 4 = 0 := by rw [pow_succ, h, zero_mul]
  have hy : y = (y - 1) + 1 := by abel
  have e2 : y ^ 2 = (y - 1) ^ 2 + 1 := by
    conv_lhs => rw [hy]
    exact hsq _
  have e4 : y ^ 4 = (y - 1) ^ 4 + 1 := by
    have : y ^ 4 = (y ^ 2) ^ 2 := by rw [← pow_mul]
    rw [this, e2, hsq, ← pow_mul]
  rw [e4, h4, zero_add]

theorem end_two_eq_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] :
    (2 : Module.End (ZMod 2) V) = 0 := by
  ext x
  simp [two_smul]
  exact add_self_eq_zero' x

end CFSG.LocalAnalysis.UniquenessCase.UCK.PairSpLem
