module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Combinatorics.Colex
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open Module

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]

@[expose] def bitSum {f : ℕ} (B : Finset (Fin f)) : ℕ := ∑ r ∈ B, 2 ^ (r : ℕ)

private theorem bitSum_map {f : ℕ} (B : Finset (Fin f)) :
    bitSum B = ∑ k ∈ B.map Fin.valEmbedding, (2 : ℕ) ^ k :=
  (Finset.sum_map B Fin.valEmbedding (fun k : ℕ => (2 : ℕ) ^ k)).symm

private theorem bitSum_injective {f : ℕ} : Function.Injective (bitSum (f := f)) := by
  intro B C h
  rw [bitSum_map, bitSum_map] at h
  exact Finset.map_injective Fin.valEmbedding (Finset.geomSum_injective le_rfl h)

private theorem bitSum_lt {f : ℕ} (B : Finset (Fin f)) : bitSum B < 2 ^ f := by
  rw [bitSum_map]
  refine Nat.geomSum_lt (by norm_num) ?_
  intro k hk
  obtain ⟨r, -, rfl⟩ := Finset.mem_map.1 hk
  exact r.isLt

private theorem bitSum_empty {f : ℕ} : bitSum (∅ : Finset (Fin f)) = 0 := by
  simp [bitSum]

private theorem image_bitSum (f : ℕ) :
    (Finset.univ : Finset (Finset (Fin f))).image bitSum = Finset.range (2 ^ f) := by
  apply Finset.eq_of_subset_of_card_le
  · intro n hn
    obtain ⟨B, -, rfl⟩ := Finset.mem_image.1 hn
    exact Finset.mem_range.2 (bitSum_lt B)
  · rw [Finset.card_range, Finset.card_image_of_injective _ bitSum_injective]
    simp

private theorem sum_range_eq_sum_bitSum {f : ℕ} {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ n ∈ Finset.range (2 ^ f), g n = ∑ B : Finset (Fin f), g (bitSum B) := by
  have hinj : Set.InjOn (bitSum (f := f)) (Finset.univ : Finset (Finset (Fin f))) :=
    fun _ _ _ _ h => bitSum_injective h
  rw [← image_bitSum f, Finset.sum_image hinj]

private theorem eval_eq_sum_bitSum {f : ℕ} (hf : Fintype.card K = 2 ^ f) (p : Polynomial K)
    (hp : p.natDegree < Fintype.card K) (t : K) :
    p.eval t = ∑ B : Finset (Fin f), t ^ bitSum B * p.coeff (bitSum B) := by
  have hn : p.natDegree < 2 ^ f := by rw [← hf]; exact hp
  rw [Polynomial.eval_eq_sum_range' hn t, sum_range_eq_sum_bitSum (fun n => p.coeff n * t ^ n)]
  exact Finset.sum_congr rfl fun B _ => mul_comm _ _

private theorem add_pow_bitSum {f : ℕ} (s t : K) (D : Finset (Fin f)) :
    (s + t) ^ bitSum D = ∑ B ∈ D.powerset, s ^ bitSum B * t ^ bitSum (D \ B) := by
  have h1 : (s + t) ^ bitSum D = ∏ r ∈ D, (s ^ 2 ^ (r : ℕ) + t ^ 2 ^ (r : ℕ)) := by
    unfold bitSum
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun r _ => add_pow_char_pow s t 2 (r : ℕ)
  rw [h1, Finset.prod_add]
  refine Finset.sum_congr rfl fun B _ => ?_
  unfold bitSum
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

private theorem sum_powerset_reindex {f : ℕ} {M : Type*} [AddCommMonoid M]
    (φ : Finset (Fin f) → Finset (Fin f) → M) :
    ∑ D : Finset (Fin f), ∑ B ∈ D.powerset, φ B D =
      ∑ B : Finset (Fin f), ∑ C : Finset (Fin f), if Disjoint B C then φ B (B ∪ C) else 0 := by
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun B => Finset.univ.filter (fun D => B ⊆ D))]
  · refine Finset.sum_congr rfl fun B _ => ?_
    rw [← Finset.sum_filter]
    refine Finset.sum_nbij' (fun D => D \ B) (fun C => B ∪ C) ?_ ?_ ?_ ?_ ?_
    · intro D hD
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
      exact Finset.disjoint_sdiff
    · intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
      exact Finset.subset_union_left
    · intro D hD
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD
      exact Finset.union_sdiff_of_subset hD
    · intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      exact Finset.union_sdiff_cancel_left hC
    · intro D hD
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD
      simp only [Finset.union_sdiff_of_subset hD]
  · intro D B
    simp [Finset.mem_powerset]

theorem coeff_eq_zero_of_sum_pow_eq_zero {f : ℕ} (hf : Fintype.card K = 2 ^ f)
    (c : Finset (Fin f) → K) (h : ∀ t : K, ∑ B : Finset (Fin f), t ^ bitSum B * c B = 0)
    (B : Finset (Fin f)) : c B = 0 := by
  set P : Polynomial K :=
    ∑ B' : Finset (Fin f), Polynomial.C (c B') * Polynomial.X ^ bitSum B' with hP
  have hdeg : P.natDegree < Fintype.card K := by
    have hle : P.natDegree ≤ 2 ^ f - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro B' _
      refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
      have := bitSum_lt B'
      omega
    have hpos : 0 < 2 ^ f := by positivity
    rw [hf]
    omega
  have heval : ∀ t : K, P.eval t = 0 := by
    intro t
    have key : P.eval t = ∑ B' : Finset (Fin f), t ^ bitSum B' * c B' := by
      rw [hP, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun B' _ => ?_
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact mul_comm _ _
    rw [key, h t]
  have hPzero : P = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P Finset.univ
      (fun t _ => heval t) (by rw [Finset.card_univ]; exact hdeg)
  have hcoeff : P.coeff (bitSum B) = c B := by
    rw [hP, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    rw [Finset.sum_eq_single B]
    · simp
    · intro B' _ hB'
      have hne : bitSum B ≠ bitSum B' := fun h' => hB' (bitSum_injective h'.symm)
      simp [hne]
    · intro hB
      exact absurd (Finset.mem_univ B) hB
  rw [← hcoeff, hPzero, Polynomial.coeff_zero]

theorem rootExpansion_unique {f : ℕ} (hf : Fintype.card K = 2 ^ f)
    (F : Finset (Fin f) → (V →ₗ[K] V))
    (h : ∀ t : K, ∑ B : Finset (Fin f), t ^ bitSum B • F B = 0) : ∀ B, F B = 0 := by
  intro B
  apply LinearMap.ext
  intro v
  rw [LinearMap.zero_apply]
  refine (Module.forall_dual_apply_eq_zero_iff K (F B v)).1 fun φ => ?_
  refine coeff_eq_zero_of_sum_pow_eq_zero hf (fun B' => φ (F B' v)) (fun t => ?_) B
  have h2 : ∑ B' : Finset (Fin f), t ^ bitSum B' • F B' v = 0 := by
    have h3 := LinearMap.congr_fun (h t) v
    simpa using h3
  have h4 := congrArg φ h2
  simpa [map_sum, map_smul, smul_eq_mul] using h4

private theorem two_var_unique {f : ℕ} (hf : Fintype.card K = 2 ^ f)
    (G : Finset (Fin f) → Finset (Fin f) → (V →ₗ[K] V))
    (h : ∀ s t : K, ∑ B : Finset (Fin f), ∑ C : Finset (Fin f),
      (s ^ bitSum B * t ^ bitSum C) • G B C = 0) :
    ∀ B C, G B C = 0 := by
  have h1 : ∀ s : K, ∀ C : Finset (Fin f), ∑ B : Finset (Fin f), s ^ bitSum B • G B C = 0 := by
    intro s
    refine rootExpansion_unique hf (fun C => ∑ B : Finset (Fin f), s ^ bitSum B • G B C) ?_
    intro t
    refine Eq.trans ?_ (h s t)
    simp only [Finset.smul_sum, smul_smul]
    refine (Finset.sum_comm).trans (Finset.sum_congr rfl fun B _ =>
      Finset.sum_congr rfl fun C _ => ?_)
    rw [mul_comm]
  intro B C
  exact rootExpansion_unique hf (fun B => G B C) (fun s => h1 s C) B

theorem exists_rootExpansion {f : ℕ} (hf : Fintype.card K = 2 ^ f) (x : K → (V →ₗ[K] V))
    (hx0 : x 0 = 1) (hx : ∀ s t, x (s + t) = x s * x t) :
    ∃ E : Finset (Fin f) → (V →ₗ[K] V),
      (∀ t : K, x t = ∑ B : Finset (Fin f), t ^ bitSum B • E B) ∧ E ∅ = 1 ∧
      (∀ B C, E B * E C = if Disjoint B C then E (B ∪ C) else 0) ∧
      ∀ B, E B ∈ Submodule.span K (Set.range x) := by
  classical
  obtain ⟨L, hLeval, hLdeg⟩ : ∃ L : K → Polynomial K,
      (∀ s t : K, (L s).eval t = if t = s then 1 else 0) ∧
      (∀ s : K, (L s).natDegree < Fintype.card K) := by
    have hinj : Set.InjOn (id : K → K) (Finset.univ : Finset K) := Function.injective_id.injOn
    refine ⟨fun s => Lagrange.basis Finset.univ id s, fun s t => ?_, fun s => ?_⟩
    · dsimp only
      by_cases hts : t = s
      · subst hts
        rw [if_pos rfl]
        exact Lagrange.eval_basis_self hinj (Finset.mem_univ _)
      · rw [if_neg hts]
        exact Lagrange.eval_basis_of_ne (v := (id : K → K)) (s := Finset.univ) (i := s) (j := t)
          (Ne.symm hts) (Finset.mem_univ t)
    · dsimp only
      rw [Lagrange.natDegree_basis hinj (Finset.mem_univ s), Finset.card_univ]
      have := Fintype.card_pos (α := K)
      omega
  obtain ⟨E, hE⟩ : ∃ E : Finset (Fin f) → (V →ₗ[K] V),
      ∀ B, E B = ∑ s : K, (L s).coeff (bitSum B) • x s :=
    ⟨fun B => ∑ s : K, (L s).coeff (bitSum B) • x s, fun B => rfl⟩
  have hexp : ∀ t : K, x t = ∑ B : Finset (Fin f), t ^ bitSum B • E B := by
    intro t
    have key : ∀ s : K, ∑ B : Finset (Fin f), t ^ bitSum B * (L s).coeff (bitSum B) =
        if t = s then 1 else 0 := by
      intro s
      rw [← hLeval s t]
      exact (eval_eq_sum_bitSum hf (L s) (hLdeg s) t).symm
    simp only [hE, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, key, ite_smul, one_smul, zero_smul]
    simp
  have hE0 : E ∅ = 1 := by
    have h0 := hexp 0
    rw [hx0, Finset.sum_eq_single (∅ : Finset (Fin f))] at h0
    · rw [bitSum_empty, pow_zero, one_smul] at h0
      exact h0.symm
    · intro B _ hB
      have hne : bitSum B ≠ 0 := fun h' => hB (bitSum_injective (h'.trans bitSum_empty.symm))
      rw [zero_pow hne, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hprod : ∀ s t : K, x s * x t =
      ∑ B : Finset (Fin f), ∑ C : Finset (Fin f), (s ^ bitSum B * t ^ bitSum C) • (E B * E C) := by
    intro s t
    rw [hexp s, hexp t, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun C _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hsum : ∀ s t : K, x (s + t) =
      ∑ B : Finset (Fin f), ∑ C : Finset (Fin f),
        (s ^ bitSum B * t ^ bitSum C) • (if Disjoint B C then E (B ∪ C) else 0) := by
    intro s t
    have hre := sum_powerset_reindex (M := V →ₗ[K] V)
      (fun B D => (s ^ bitSum B * t ^ bitSum (D \ B)) • E D)
    beta_reduce at hre
    rw [hexp (s + t)]
    simp only [add_pow_bitSum, Finset.sum_smul]
    rw [hre]
    refine Finset.sum_congr rfl fun B _ => Finset.sum_congr rfl fun C _ => ?_
    by_cases hBC : Disjoint B C
    · simp only [if_pos hBC, Finset.union_sdiff_cancel_left hBC]
    · simp only [if_neg hBC, smul_zero]
  have hG : ∀ B C : Finset (Fin f), E B * E C - (if Disjoint B C then E (B ∪ C) else 0) = 0 := by
    refine two_var_unique hf
      (fun B C => E B * E C - (if Disjoint B C then E (B ∪ C) else 0)) ?_
    intro s t
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← hprod s t, ← hsum s t, ← hx s t, sub_self]
  have hmem : ∀ B, E B ∈ Submodule.span K (Set.range x) := fun B => by
    rw [hE B]
    exact Submodule.sum_mem _ fun s _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self s))
  exact ⟨E, hexp, hE0, fun B C => sub_eq_zero.1 (hG B C), hmem⟩

end CFSG.RankThree.GF2n.Smith81.S81V
