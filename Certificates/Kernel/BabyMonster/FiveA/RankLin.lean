module

public import CFSG.Certificates.Kernel.BabyMonster.FixSound

public section

namespace CertificateChecks.KernelBM.FiveA

open Module CFSG.KC.BM CFSG.KC.BM.Fix
open scoped Matrix

section Lin

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

end Lin

theorem rank_sub_one_of_cert {M P R : List Nat} {k : ℕ} (hk : k ≤ 4370)
    (hM : wfMat M = true) (hP : wfMat P = true) (hR : wfMat R = true)
    (hrk : AllStripsX M P R) (hs : shapeOK R k = true) (he : echFrom P k = true) :
    (stripMat M - 1).rank = k := by
  have hmul := stripMat_mul_add_one hM hP hrk
  have hs' := shapeOK_sound hR hs
  have he' := echFrom_sound hP he
  have e : stripMat M - 1 = stripMat M + 1 := by
    ext i j
    rw [Matrix.sub_apply, Matrix.add_apply]
    exact CharTwo.sub_eq_add _ _
  rw [e]
  apply le_antisymm
  · have hK := card_le_kerL (A := stripMat M + 1)
      (fun i : {i : Fin 4370 // k ≤ i.val} => stripMat P i)
      (fun i => by rw [← rowMul, hmul]; exact hs'.2 i i.2) he'
    rw [card_ge 4370 k hk] at hK
    have := finrank_kerL (stripMat M + 1)
    omega
  · have h1 := card_le_rank (A := stripMat R) (fun i : {i : Fin 4370 // i.val < k} => i.1) hs'.1
    rw [card_lt 4370 k hk, ← hmul] at h1
    exact h1.trans (Matrix.rank_mul_le_right _ _)

theorem ne_one_of_rank {M : Matrix (Fin 4370) (Fin 4370) (ZMod 2)} {k : ℕ} (h : (M - 1).rank = k)
    (hk : k ≠ 0) : M ≠ 1 := by
  rintro rfl
  rw [sub_self, Matrix.rank_zero] at h
  exact hk h.symm

end CertificateChecks.KernelBM.FiveA

end
