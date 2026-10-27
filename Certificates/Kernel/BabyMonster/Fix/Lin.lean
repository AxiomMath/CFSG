module

public import Mathlib.LinearAlgebra.Matrix.Rank

public section

namespace CertificateChecks.KernelBM.Fix

open Module
open scoped Matrix

variable {K : Type*} [Field K] {n : ℕ}

@[expose] noncomputable def kerL (A : Matrix (Fin n) (Fin n) K) : Submodule K (Fin n → K) :=
  LinearMap.ker Aᵀ.mulVecLin

theorem mem_kerL {A : Matrix (Fin n) (Fin n) K} {y : Fin n → K} : y ∈ kerL A ↔ y ᵥ* A = 0 := by
  rw [kerL, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]

theorem finrank_kerL (A : Matrix (Fin n) (Fin n) K) : finrank K (kerL A) + A.rank = n := by
  have h := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  rw [Module.finrank_fin_fun] at h
  rw [kerL, ← Matrix.rank_transpose A, Matrix.rank]
  omega

theorem card_le_rank {A : Matrix (Fin n) (Fin n) K} {ι : Type*} [Fintype ι] (f : ι → Fin n)
    (h : LinearIndependent K fun i => A (f i)) : Fintype.card ι ≤ A.rank := by
  rw [Matrix.rank_eq_finrank_span_row]
  let b : ι → Submodule.span K (Set.range A.row) :=
    fun i => ⟨A (f i), Submodule.subset_span ⟨f i, rfl⟩⟩
  have hb : LinearIndependent K ((Submodule.span K (Set.range A.row)).subtype ∘ b) := h
  exact (LinearIndependent.of_comp _ hb).fintype_card_le_finrank

theorem card_le_kerL {A : Matrix (Fin n) (Fin n) K} {ι : Type*} [Fintype ι] (v : ι → Fin n → K)
    (hv : ∀ i, v i ᵥ* A = 0) (h : LinearIndependent K v) : Fintype.card ι ≤ finrank K (kerL A) := by
  let b : ι → kerL A := fun i => ⟨v i, mem_kerL.2 (hv i)⟩
  have hb : LinearIndependent K ((kerL A).subtype ∘ b) := h
  exact (LinearIndependent.of_comp _ hb).fintype_card_le_finrank

theorem mem_span_of_finrank_le_one {S : Submodule K (Fin n → K)} (h : finrank K S ≤ 1)
    {f y : Fin n → K} (hf : f ∈ S) (hy : y ∈ S) (hf0 : f ≠ 0) : ∃ c : K, c • f = y := by
  have hspan : Submodule.span K {f} = S :=
    Submodule.eq_of_le_of_finrank_le (Submodule.span_le.2 (Set.singleton_subset_iff.2 hf))
      (h.trans (finrank_span_singleton hf0).ge)
  rw [← hspan] at hy
  exact Submodule.mem_span_singleton.1 hy

theorem rowMul (P A : Matrix (Fin n) (Fin n) K) (i : Fin n) : (P * A) i = P i ᵥ* A := by
  funext j
  rw [Matrix.mul_apply, Matrix.vecMul, dotProduct]

theorem card_lt (m k : ℕ) (hk : k ≤ m) : Fintype.card {i : Fin m // i.val < k} = k := by
  rw [Fintype.card_subtype]
  have := Fin.card_filter_val_lt (n := m) (m := k)
  rw [this]
  omega

theorem card_ge (m k : ℕ) (hk : k ≤ m) : Fintype.card {i : Fin m // k ≤ i.val} = m - k := by
  have e : Fintype.card {i : Fin m // k ≤ i.val} = Fintype.card {i : Fin m // ¬ i.val < k} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => not_lt.symm)
  rw [e, Fintype.card_subtype_compl, card_lt m k hk, Fintype.card_fin]

end CertificateChecks.KernelBM.Fix

end
