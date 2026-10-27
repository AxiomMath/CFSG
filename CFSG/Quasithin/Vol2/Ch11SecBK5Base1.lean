module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K5

open Polynomial

variable {K : Type} [Field K]


theorem aeval_eq_zero_of_dvd (M : Matrix (Fin 2) (Fin 2) K) {g : K[X]} (h : M.charpoly ∣ g) :
    aeval M g = 0 := by
  obtain ⟨r, rfl⟩ := h
  rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]

theorem pow_sq_of_pow (M : Matrix (Fin 2) (Fin 2) K) {q : ℕ} (h : M ^ q = M) : M ^ (q ^ 2) = M := by
  rw [sq, pow_mul, h, h]

theorem pow_card_of_dvd [Finite K] (M : Matrix (Fin 2) (Fin 2) K)
    (h : M.charpoly ∣ X ^ (Nat.card K ^ 2) - X) : M ^ (Nat.card K ^ 2) = M := by
  have := aeval_eq_zero_of_dvd M h
  rwa [map_sub, map_pow, aeval_X, sub_eq_zero] at this

theorem dvd_of_irreducible [Finite K] {P : K[X]} (hP : Irreducible P) (h2 : P.natDegree = 2) :
    P ∣ X ^ (Nat.card K ^ 2) - X := by
  have : Fact (Irreducible P) := ⟨hP⟩
  have hP0 : P ≠ 0 := hP.ne_zero
  let pb := AdjoinRoot.powerBasis hP0
  have : Module.Finite K (AdjoinRoot P) := pb.finite
  have : Finite (AdjoinRoot P) := Module.finite_of_finite K
  have : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  have hcard : Nat.card (AdjoinRoot P) = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), pb.finrank, AdjoinRoot.powerBasis_dim, h2]
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, ← hcard,
    Nat.card_eq_fintype_card, FiniteField.pow_card, sub_self]

theorem dvd_of_two_roots [Finite K] {α β : K} (hαβ : α ≠ β) :
    (X - C α) * (X - C β) ∣ X ^ Nat.card K - X := by
  have := Fintype.ofFinite K
  have hroot : ∀ a : K, (X - C a) ∣ X ^ Nat.card K - X := fun a => by
    rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, eval_X, Nat.card_eq_fintype_card,
      FiniteField.pow_card, sub_self]
  exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hαβ).isUnit).mul_dvd (hroot α)
    (hroot β)

theorem smul_one_pow_card_sq [Finite K] (c : K) :
    (c • (1 : Matrix (Fin 2) (Fin 2) K)) ^ (Nat.card K ^ 2) = c • 1 := by
  have := Fintype.ofFinite K
  rw [_root_.smul_pow, one_pow, sq, pow_mul, Nat.card_eq_fintype_card, FiniteField.pow_card,
    FiniteField.pow_card]

theorem pow_card_sq_of_odd [Finite K] [CharP K 2] (M : Matrix (Fin 2) (Fin 2) K) {k : ℕ}
    (hk : Odd k) {ν : K} (hν : ν ≠ 0) (hM : M ^ k = ν • 1) : M ^ (Nat.card K ^ 2) = M := by
  have hP := Matrix.charpoly_fin_two M
  have hdeg : M.charpoly.natDegree = 2 := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  by_cases hirr : Irreducible M.charpoly
  · exact pow_card_of_dvd M (dvd_of_irreducible hirr hdeg)
  have hroots : M.charpoly.roots ≠ 0 := fun h =>
    hirr ((irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)).mpr h)
  obtain ⟨α, hα⟩ := Multiset.exists_mem_of_ne_zero hroots
  have hαr : M.charpoly.eval α = 0 :=
    (mem_roots (Matrix.charpoly_monic M).ne_zero).mp hα
  set β := M.trace - α with hβ
  have hδ : M.det = α * β := by
    rw [hP] at hαr
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C] at hαr
    rw [hβ]
    linear_combination hαr
  have hfact : M.charpoly = (X - C α) * (X - C β) := by
    rw [hP, hδ, hβ, C_mul, C_sub]
    ring
  have hCH := Matrix.aeval_self_charpoly M
  rw [hfact] at hCH
  simp only [map_mul, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at hCH
  by_cases hαβ : α = β
  ·
    rw [← hαβ] at hCH
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : M * M = (α * α) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have e : (M - α • 1) * (M - α • 1) =
          M * M - (α * α) • (1 : Matrix (Fin 2) (Fin 2) K) - (2 * α) • (M - α • 1) := by
        rw [sub_mul, mul_sub, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
          Matrix.smul_mul, one_mul, mul_one, mul_one, smul_smul, mul_smul, two_mul, add_smul]
        simp only [smul_sub]
        abel
      rw [e, h2, zero_mul, zero_smul, sub_zero, sub_eq_zero] at hCH
      exact hCH
    obtain ⟨j, rfl⟩ := hk
    have hpow : M ^ (2 * j + 1) = (α * α) ^ j • M := by
      rw [pow_succ, pow_mul, sq, hsq, _root_.smul_pow, one_pow, smul_mul_assoc, one_mul]
    rw [hpow] at hM
    by_cases hα0 : α * α = 0
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [pow_zero, one_smul] at hM
        rw [hM]
        exact smul_one_pow_card_sq ν
      · rw [hα0, zero_pow hj.ne', zero_smul] at hM
        have h3 := congrFun (congrFun hM 0) 0
        simp only [Matrix.zero_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
          mul_one] at h3
        exact absurd h3.symm hν
    · have hM' : M = ((α * α) ^ j)⁻¹ • ν • (1 : Matrix (Fin 2) (Fin 2) K) := by
        rw [← hM, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hα0), one_smul]
      rw [hM', smul_smul]
      exact smul_one_pow_card_sq _
  ·
    have h1 : M ^ Nat.card K = M := by
      have := aeval_eq_zero_of_dvd M (hfact ▸ dvd_of_two_roots hαβ)
      rwa [map_sub, map_pow, aeval_X, sub_eq_zero] at this
    exact pow_sq_of_pow M h1

end CFSG.Quasithin.Vol2.Ch11.SecB.K5
