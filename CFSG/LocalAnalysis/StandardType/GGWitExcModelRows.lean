module

public import CFSG.LocalAnalysis.StandardType.GGWitExcModelSound
public import CFSG.LocalAnalysis.StandardType.GGWitExcModelTransfer

public section

namespace CFSG.StandardType.ZS

open Certificates.ExcModel

theorem owEm_ctList_sound : ∀ w ∈ ctList (), w ∈ ctRoots := by
  intro w hw
  simp only [ctList, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and] at hw
  rcases hw with ⟨i, j, hw⟩ | ⟨t1, ht1, t2, ht2, t3, ht3, t4, ht4, t5, ht5, hw⟩
  · by_cases hij : i < j
    · rw [if_pos hij, List.mem_map] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      exact Or.inl ⟨i, j, hij, k, List.mem_range.mp hk, rfl⟩
    · rw [if_neg hij] at hw
      simp at hw
  · by_cases hs : (t1 + t2 + t3 + t4 + t5) % 3 = 0
    · rw [if_pos hs, List.mem_singleton] at hw
      subst hw
      refine Or.inr ⟨![0, t1, t2, t3, t4, t5], rfl, ?_, ?_, rfl⟩
      · intro i
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht1 ht2 ht3 ht4 ht5
        fin_cases i <;> simp <;> omega
      · simp [Fin.sum_univ_succ]
        omega
    · rw [if_neg hs] at hw
      simp at hw

theorem owEm_ctList_complete : ∀ w ∈ ctRoots, w ∈ ctList () := by
  rintro w (⟨i, j, hij, k, hk, rfl⟩ | ⟨t, h0, hlt, hsum, rfl⟩)
  · simp only [ctList, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
    left
    refine ⟨i, j, ?_⟩
    rw [if_pos hij, List.mem_map]
    exact ⟨k, List.mem_range.mpr hk, rfl⟩
  · simp only [ctList, List.mem_append, List.mem_flatMap, List.mem_finRange, true_and]
    right
    have ht : t = ![0, t 1, t 2, t 3, t 4, t 5] := by
      funext m
      fin_cases m <;> simp [h0]
    have hsum' : (t 1 + t 2 + t 3 + t 4 + t 5) % 3 = 0 := by
      simp [Fin.sum_univ_succ, h0] at hsum
      omega
    have h1 := hlt 1
    have h2 := hlt 2
    have h3 := hlt 3
    have h4 := hlt 4
    have h5 := hlt 5
    refine ⟨t 1, by simp; omega, t 2, by simp; omega, t 3, by simp; omega, t 4, by simp; omega, t 5,
      by simp; omega, ?_⟩
    rw [if_pos hsum', List.mem_singleton]
    rw [← ht]

theorem owEm_rank_vecMulVec_field {K : Type*} [Field K] {n : ℕ} (u v : Fin n → K) (hu : u ≠ 0) (hv : v ≠ 0) :
    (Matrix.vecMulVec u v).rank = 1 := by
  apply le_antisymm (Matrix.rank_vecMulVec_le u v)
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    exact hv (funext fun j => not_not.mp (not_exists.mp h j))
  by_contra hlt
  have h0 : (Matrix.vecMulVec u v).rank = 0 := by omega
  have hbot : LinearMap.range (Matrix.vecMulVec u v).mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hz : (Matrix.vecMulVec u v).mulVecLin (Pi.single j 1) = 0 := by
    have : (Matrix.vecMulVec u v).mulVecLin (Pi.single j 1) ∈ LinearMap.range (Matrix.vecMulVec u v).mulVecLin :=
      LinearMap.mem_range_self _ _
    rw [hbot] at this
    exact (Submodule.mem_bot _).mp this
  rw [Matrix.mulVecLin_apply, Matrix.vecMulVec_mulVec, dotProduct_single, mul_one] at hz
  rcases smul_eq_zero.mp hz with h | h
  · exact hj (by simpa using h)
  · exact hu h

theorem owEm_rank_vecMulVec {n : ℕ} (u v : Fin n → ZMod 13) (hu : u ≠ 0) (hv : v ≠ 0) :
    (Matrix.vecMulVec u v).rank = 1 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact owEm_rank_vecMulVec_field u v hu hv

theorem owEm_isReflMat_of_outer {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) (ZMod 13))
    (hg : (g : Mat n) * g = 1) (u v : Fin n → ZMod 13) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : (g : Mat n) - 1 = Matrix.vecMulVec u v) : IsReflMat g := by
  refine ⟨Units.ext (by simpa using hg), ?_⟩
  rw [h]
  exact owEm_rank_vecMulVec u v hu hv

theorem owEm_piMat_sub_one : (piMat 0 1 1 : Mat 4) - 1 = Matrix.vecMulVec ![1, -1, 0, 0] ![-1, 1, 0, 0] := by
  decide +kernel

theorem owEm_ctList_nz : ∀ w ∈ ctList (), w.1 ≠ 0 ∧ w.2 ≠ 0 ∧ ∑ i, w.1 i * w.2 i ≠ 0 := by
  have h : (ctList ()).all (fun w => decide (w.1 ≠ 0) && decide (w.2 ≠ 0) && decide (∑ i, w.1 i * w.2 i ≠ 0)) = true := by
    decide +kernel
  intro w hw
  have := List.all_eq_true.mp h w hw
  obtain ⟨⟨h1, h2⟩, h3⟩ : (¬w.1 = 0 ∧ ¬w.2 = 0) ∧ ¬∑ i, w.1 i * w.2 i = 0 := by simpa using this
  exact ⟨h1, h2, h3⟩

theorem owEm_one_sub_smul (v vb : Fin 6 → ZMod 13) (c : ZMod 13) :
    (1 - c • Matrix.of fun r s => v r * vb s : Mat 6) - 1 = Matrix.vecMulVec ((-c) • v) vb := by
  change (1 - c • Matrix.vecMulVec v vb : Mat 6) - 1 = _
  rw [Matrix.smul_vecMulVec]
  calc
    (1 - c • Matrix.vecMulVec v vb : Mat 6) - 1 = -(c • Matrix.vecMulVec v vb) :=
      _root_.sub_sub_cancel_left _ _
    _ = (-c) • Matrix.vecMulVec v vb := by
      ext i j
      change -(c * (v i * vb j)) = (-c) * (v i * vb j)
      exact (_root_.neg_mul c (v i * vb j)).symm

local instance owEm_factPrimeThirteen : Fact (Nat.Prime 13) := ⟨by norm_num⟩

theorem owEm_herRefl_sub_one (v vb : Fin 6 → ZMod 13) :
    herRefl v vb - 1 = Matrix.vecMulVec (-((2 : ZMod 13) / ∑ i, v i * vb i) • v) vb := by
  unfold herRefl
  exact owEm_one_sub_smul v vb _

theorem owEm_herRefl_isReflMat (w : (Fin 6 → ZMod 13) × (Fin 6 → ZMod 13)) (hw : w ∈ ctList ())
    (g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 13)) (hg : (g : Mat 6) = herRefl w.1 w.2)
    (hgg : (g : Mat 6) * g = 1) : IsReflMat g := by
  obtain ⟨h1, h2, h3⟩ := owEm_ctList_nz w hw
  refine owEm_isReflMat_of_outer g hgg _ w.2 ?_ h2 (by rw [hg, owEm_herRefl_sub_one])
  exact smul_ne_zero (neg_ne_zero.mpr (div_ne_zero (by decide) h3)) h1

end CFSG.StandardType.ZS

end
