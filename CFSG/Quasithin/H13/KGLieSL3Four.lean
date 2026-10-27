module

public import CFSG.Quasithin.H13.KGLiePair

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

section Field4

variable {K : Type} [Field K]

theorem exists_omega [Finite K] (hK : Nat.card K = 4) : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ω, hω0, hω1⟩ : ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
    by_contra h
    push Not at h
    have hle : Nat.card K ≤ Nat.card Bool :=
      Nat.card_le_card_of_surjective (fun b : Bool => if b then (1 : K) else 0) (by
        intro c
        by_cases hc : c = 0
        · exact ⟨false, by simp [hc]⟩
        · exact ⟨true, by simp [h c hc]⟩)
    rw [hK, Nat.card_eq_fintype_card, Fintype.card_bool] at hle
    omega
  refine ⟨ω, ?_⟩
  have h3 : ω ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one ω hω0
    rwa [← Nat.card_eq_fintype_card, hK] at this
  have hm : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.1 hm with h | h
  · exact absurd (sub_eq_zero.1 h) hω1
  · exact h

theorem sq_root_omega {ω : K} (h : ω ^ 2 + ω + 1 = 0) : (ω ^ 2) ^ 2 + ω ^ 2 + 1 = 0 := by
  linear_combination (ω ^ 2 - ω + 1) * h

theorem charP_two_of_card_four [Finite K] (hK : Nat.card K = 4) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)

theorem transvection_mulVec {n : Type} [Fintype n] [DecidableEq n] (i j : n) (c : K)
    (x : n → K) : Matrix.transvection i j c *ᵥ x = x + Pi.single i (c * x j) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

end Field4

section SL3

variable {K : Type} [Field K]

theorem exists_pairTrace_sl3 [Finite K] (hK : Nat.card K = 4) (u₀ : Fin 3 → K)
    (φ : (Fin 3 → K) →ₗ[K] K) (hu : u₀ ≠ 0) (hφ : φ ≠ 0) (hφu : φ u₀ = 0) :
    ∃ γ : ↥(StatedSL 3 K), pairTrace φ u₀ γ ^ 2 + pairTrace φ u₀ γ + 1 = 0 := by
  classical
  have : CharP K 2 := charP_two_of_card_four hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set f : Fin 3 → K := fun i => φ (fun j => if i = j then 1 else 0) with hf
  have hφx : ∀ x : Fin 3 → K, φ x = ∑ i, x i * f i := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ φ x]
    rfl
  obtain ⟨i, j, hij, hd⟩ : ∃ i j : Fin 3, i ≠ j ∧ u₀ j * f i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j₀, hj₀⟩ : ∃ j, u₀ j ≠ 0 := by
      by_contra h
      push Not at h
      exact hu (funext h)
    obtain ⟨i₀, hi₀⟩ : ∃ i, f i ≠ 0 := by
      by_contra h
      push Not at h
      apply hφ
      refine LinearMap.ext fun x => ?_
      rw [hφx, LinearMap.zero_apply]
      simp [h]
    by_cases hk : i₀ = j₀
    · subst hk
      have hu' : ∀ j, j ≠ i₀ → u₀ j = 0 := fun j hj =>
        (mul_eq_zero.1 (hcon i₀ j (Ne.symm hj))).resolve_right hi₀
      have hφ' : φ u₀ = u₀ i₀ * f i₀ := by
        rw [hφx, Finset.sum_eq_single i₀]
        · intro b _ hb
          rw [hu' b hb, zero_mul]
        · simp
      rw [hφu] at hφ'
      exact mul_ne_zero hj₀ hi₀ hφ'.symm
    · exact mul_ne_zero hj₀ hi₀ (hcon i₀ j₀ hk)
  obtain ⟨ω, hω⟩ := exists_omega hK
  set d := u₀ j * f i with hd'
  set c := ω * d⁻¹ with hc
  have hcd : c * d = ω := by rw [hc, mul_assoc, inv_mul_cancel₀ hd, mul_one]
  have hmul : ∀ a b : K,
      Matrix.transvection i j a * Matrix.transvection i j b = Matrix.transvection i j (a + b) :=
    fun a b => Matrix.transvection_mul_transvection_same i j hij a b
  set t : Matrix.GeneralLinearGroup (Fin 3) K :=
    ⟨Matrix.transvection i j c, Matrix.transvection i j (-c),
      by rw [hmul, add_neg_cancel, Matrix.transvection_zero],
      by rw [hmul, neg_add_cancel, Matrix.transvection_zero]⟩ with ht
  have htSL : t ∈ StatedSL 3 K := Subgroup.subset_closure (Matrix.det_transvection_of_ne i j hij c)
  refine ⟨⟨t, htSL⟩, ?_⟩
  have hmv : ∀ a : K, φ (Matrix.transvection i j a *ᵥ u₀) = a * d := by
    intro a
    rw [transvection_mulVec, map_add, hφu, zero_add, hφx, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, hd']
      ring
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_mul]
    · simp
  have hpt : pairTrace φ u₀ (⟨t, htSL⟩ : ↥(StatedSL 3 K)) = ω ^ 2 := by
    show φ (Matrix.transvection i j c *ᵥ u₀) * φ (Matrix.transvection i j (-c) *ᵥ u₀) = ω ^ 2
    rw [hmv, hmv]
    linear_combination (-(c * d + ω)) * hcd - ω ^ 2 * h2
  rw [hpt]
  exact sq_root_omega hω

end SL3

section Row

variable {V : Type} [CommGroup V] [Finite V]

theorem factLieSL3FourRow1321_holds : A5.FactLieSL3FourRow1321 := by
  intro V _ _ hV2 G L v hB4 hc h
  obtain ⟨K, _, _, hK, hr⟩ := h
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  exact false_of_nat_four hV2 hB4 hc (ι := Fin 3) (by simp) hK4 hr
    (fun u₀ φ hu hφ hφu => exists_pairTrace_sl3 hK4 u₀ φ hu hφ hφu)

end Row

end CFSG.Quasithin.H13.KGLie
