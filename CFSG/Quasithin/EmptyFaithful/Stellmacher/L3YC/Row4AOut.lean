module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

namespace Stellmacher.L3YC

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification Matrix CFSG.Open

theorem eq_zero_or_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (r : K) :
    r = 0 ∨ r = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hc : ({0, 1} : Finset K).card = Fintype.card K := by
    rw [Finset.card_pair zero_ne_one, ← Nat.card_eq_fintype_card, hK]
  have h := Finset.eq_univ_of_card _ hc
  have hr' : r ∈ ({0, 1} : Finset K) := h ▸ Finset.mem_univ r
  simpa using hr'

theorem ringEquiv_eq_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (σ : K ≃+* K) : σ = 1 := by
  ext x
  rcases eq_zero_or_one_of_card_two hK x with rfl | rfl <;> simp

theorem conjAut_mem_range_of_card_two {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (A : GL (Fin n) K) :
    conjAut n K A ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  have hdet : (A : Matrix (Fin n) (Fin n) K).det = 1 := by
    have h := eq_zero_or_one_of_card_two hK (A : Matrix (Fin n) (Fin n) K).det
    rcases h with h | h
    · exact absurd h (by
        rw [← Matrix.GeneralLinearGroup.val_det_apply]
        exact (Matrix.GeneralLinearGroup.det A).ne_zero)
    · exact h
  set a : SpecialLinearGroup (Fin n) K := ⟨(A : Matrix (Fin n) (Fin n) K), hdet⟩ with ha
  refine ⟨proj n K a, ?_⟩
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  have hinv : ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h1 : ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (A : Matrix (Fin n) (Fin n) K) = 1 := by
      have := congrArg (fun z : SpecialLinearGroup (Fin n) K =>
        (z : Matrix (Fin n) (Fin n) K)) (inv_mul_cancel a)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
      exact this
    calc ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((A : Matrix (Fin n) (Fin n) K) * ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [← mul_assoc, h1, one_mul]
  have hconj : CatalogueBHigherLinearAction.slConjugation n K A g = a * g * a⁻¹ := by
    apply Subtype.ext
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      hinv]
  rw [conjAut_proj, hconj]
  simp [MulAut.conj_apply]

theorem inner_of_three_pow_projectiveSL {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (α : MulAut (projectiveSL n K)) {m : ℕ} (hα : α ^ 3 ^ m = 1) :
    α ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  obtain ⟨A, σ, ε, hε, h⟩ := (automorphism_generation (K := K) hn).2 α
  rw [ringEquiv_eq_one_of_card_two hK σ, map_one, mul_one] at h
  obtain ⟨p, hp⟩ := conjAut_mem_range_of_card_two (n := n) hK A
  have hδδ : dualAut n K * dualAut n K = 1 := standard_automorphism_transport.2.2.2.1
  have hnorm : ∀ (φ : MulAut (projectiveSL n K)) (q : projectiveSL n K),
      φ * MulAut.conj q * φ⁻¹ = MulAut.conj (φ q) := by
    intro φ q
    ext x
    simp [MulAut.conj_apply]
  have hsq : α ^ 2 ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
    interval_cases ε
    · rw [pow_zero, mul_one] at h
      rw [h, ← hp]
      exact ⟨p ^ 2, by simp⟩
    · rw [pow_one] at h
      refine ⟨p * dualAut n K p, ?_⟩
      have hδinv : (dualAut n K)⁻¹ = dualAut n K := inv_eq_of_mul_eq_one_right hδδ
      have : α ^ 2 = MulAut.conj p * (dualAut n K * MulAut.conj p * (dualAut n K)⁻¹) *
          (dualAut n K * dualAut n K) := by
        rw [pow_two, h, ← hp]
        group
      rw [this, hnorm, hδδ, mul_one, ← map_mul]
  obtain ⟨k, hk⟩ := (Odd.pow (by decide : Odd 3) : Odd (3 ^ m))
  have h1 : (α ^ 2) ^ k * α = 1 := by
    rw [← pow_mul, ← pow_succ, ← hk]
    exact hα
  have h2 : α = ((α ^ 2) ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h1
  rw [h2]
  exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hsq k)

theorem inner_of_three_pow_PSL2 {X : Type} [Group X] {n : ℕ} (hn : 3 ≤ n) (hX : IsPSL n 2 1 X)
    (τ : MulAut X) {m : ℕ} (hτ : τ ^ 3 ^ m = 1) : ∃ x : X, τ = MulAut.conj x := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hK2 : Nat.card K = 2 := by simpa using hK
  let e' : X ≃* projectiveSL n K :=
    e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj n K).symm
  have hα : (MulAut.congr e' τ) ^ 3 ^ m = 1 := by
    rw [← map_pow, hτ, map_one]
  obtain ⟨p, hp⟩ := inner_of_three_pow_projectiveSL hn hK2 _ hα
  refine ⟨e'.symm p, ?_⟩
  ext x
  apply e'.injective
  have := congrArg (fun φ : MulAut (projectiveSL n K) => φ (e' x)) hp
  simp only [MulAut.congr_apply, MulAut.conj_apply] at this
  simpa [MulAut.conj_apply] using this.symm

theorem inner_of_three_pow_L42 {X : Type} [Group X] (hX : IsPSL 4 2 1 X) (τ : MulAut X) {m : ℕ}
    (hτ : τ ^ 3 ^ m = 1) : ∃ x : X, τ = MulAut.conj x :=
  inner_of_three_pow_PSL2 (by norm_num) hX τ hτ

end Stellmacher.L3YC

end CFSG.Quasithin
