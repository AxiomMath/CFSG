module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped Matrix

theorem alg_sing_quadratic_add_smul {K : Type} [Field K] {M : Type} [AddCommGroup M]
    [Module K M] (Q : QuadraticMap K M K) (v w : M) (c : K) :
    Q (v + c • w) = Q v + c * c * Q w + c * QuadraticMap.polar Q v w := by
  rw [QuadraticMap.map_add Q v (c • w), QuadraticMap.map_smul, QuadraticMap.polar_smul_right]
  simp only [smul_eq_mul]

theorem alg_sing_invariant_of_involution {K : Type} [Field K] [CharP K 2] {M : Type}
    [AddCommGroup M] [Module K M] (Q : QuadraticMap K M K) (f : M → M)
    (hff : ∀ v, f (f v) = v) {μ : K} (hμ : ∀ v, Q (μ • f v) = Q v) {v₀ : M}
    (hv₀ : Q v₀ ≠ 0) :
    ∀ v, Q (f v) = Q v := by
  have h1 : ∀ v, μ * μ * Q (f v) = Q v := by
    intro v
    have h := hμ v
    rw [QuadraticMap.map_smul, smul_eq_mul] at h
    exact h
  have h2 : ∀ v, μ * μ * Q v = Q (f v) := by
    intro v
    have h := h1 (f v)
    rw [hff] at h
    exact h
  have h3 : ∀ v, Q v = μ * μ * (μ * μ * Q v) := by
    intro v
    rw [h2 v, h1 v]
  have hm : (μ * μ * (μ * μ) - 1) * Q v₀ = 0 := by
    linear_combination (-1 : K) * h3 v₀
  have hm' : μ * μ * (μ * μ) = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hv₀)
  have h2' : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hsq : (μ * μ - 1) * (μ * μ - 1) = 0 := by
    linear_combination hm' + (1 - μ * μ) * h2'
  have hm1 : μ * μ = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
  intro v
  have h := h1 v
  rw [hm1, one_mul] at h
  exact h

theorem alg_sing_exists_ne_zero_ne_one (K : Type) [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  haveI : Fintype K := Fintype.ofFinite K
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
    intro c _
    by_cases h : c = 0
    · simp [h]
    · simp [hcon c h]
  have hle : (Finset.univ : Finset K).card ≤ 2 :=
    (Finset.card_le_card hsub).trans Finset.card_le_two
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
  omega

theorem alg_sing_of_family {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Q : QuadraticForm K (ι → K)}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) {X : Subgroup (GL ι K)}
    (hN : ∀ A : GL ι K, (∀ g ∈ X, A * g * A⁻¹ ∈ X) →
      ∃ c : K, c ≠ 0 ∧ ∀ v, Q (c • ((A : Matrix ι ι K) *ᵥ v)) = Q v)
    (T : (ι → K) →ₗ[K] (ι → K)) (hT2 : ∀ v, T (T v) = 0)
    (hfam : ∀ c : K, ∃ A : GL ι K, (∀ v, (A : Matrix ι ι K) *ᵥ v = v + c • T v) ∧
      ∀ g ∈ X, A * g * A⁻¹ ∈ X) :
    ∀ v, Q (T v) = 0 := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : ι → K, Q v₀ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hzero : (Pi.single i (1 : K) : ι → K) = 0 :=
      hnd.1 _ fun w => by
        rw [QuadraticMap.polarBilin_apply_apply]
        simp [QuadraticMap.polar, hcon]
    have h1 := congrFun hzero i
    simp at h1
  obtain ⟨c₀, hc0, hc1⟩ := alg_sing_exists_ne_zero_ne_one K hK
  intro v
  have hE : ∀ c : K, c * c * Q (T v) + c * QuadraticMap.polar Q v (T v) = 0 := by
    intro c
    obtain ⟨A, hA, hAX⟩ := hfam c
    obtain ⟨μ, -, hμ⟩ := hN A hAX
    have hff : ∀ w, (A : Matrix ι ι K) *ᵥ ((A : Matrix ι ι K) *ᵥ w) = w := by
      intro w
      have hTw : T ((A : Matrix ι ι K) *ᵥ w) = T w := by
        rw [hA w, map_add, map_smul, hT2, smul_zero, add_zero]
      rw [hA ((A : Matrix ι ι K) *ᵥ w), hTw, hA w, add_assoc, ← add_smul,
        CharTwo.add_self_eq_zero, zero_smul, add_zero]
    have hQA : ∀ w, Q ((A : Matrix ι ι K) *ᵥ w) = Q w :=
      alg_sing_invariant_of_involution Q (fun w => (A : Matrix ι ι K) *ᵥ w) hff hμ hv₀
    have h := hQA v
    rw [hA v, alg_sing_quadratic_add_smul] at h
    linear_combination h
  have h1E := hE 1
  have hc0E := hE c₀
  have key : c₀ * (1 - c₀) * Q (T v) = 0 := by
    linear_combination c₀ * h1E - hc0E
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (mul_ne_zero hc0 (sub_ne_zero.mpr (Ne.symm hc1)))
  · exact h

end CFSG.RankThree.GF2n.Stroth80
