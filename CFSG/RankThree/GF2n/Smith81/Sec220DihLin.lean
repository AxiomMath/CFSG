module

public import CFSG.RankThree.GF2n.Smith81.Sec220TvLemmas

public section

namespace CFSG.RankThree.GF2n.Smith81

open Matrix

section DihTv

variable {K : Type} [Field K] {n : ℕ}

@[expose] def dihTv (p r : Fin n → K) : Matrix (Fin n) (Fin n) K := 1 + vecMulVec p r

theorem dihTv_mulVec (p r x : Fin n → K) : dihTv p r *ᵥ x = x + (r ⬝ᵥ x) • p := by
  unfold dihTv
  rw [add_mulVec, one_mulVec]
  congr 1
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

theorem dihTv_det (p r : Fin n → K) : (dihTv p r).det = 1 + r ⬝ᵥ p := by
  unfold dihTv
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

theorem exists_eq_dihTv_of_rank_eq_one {M : Matrix (Fin n) (Fin n) K} (h : (M - 1).rank = 1)
    (hdet : M.det = 1) : ∃ p r : Fin n → K, p ≠ 0 ∧ r ≠ 0 ∧ r ⬝ᵥ p = 0 ∧ M = dihTv p r := by
  set N := M - 1 with hNdef
  have hfin : Module.finrank K (LinearMap.range N.mulVecLin) = 1 := h
  obtain ⟨v, hv⟩ : ∃ v : LinearMap.range N.mulVecLin, v ≠ 0 :=
    Module.finrank_pos_iff_exists_ne_zero.mp (by rw [hfin]; exact Nat.one_pos)
  have hspan := (finrank_eq_one_iff_of_nonzero' v hv).mp hfin
  set p : Fin n → K := (v : Fin n → K) with hpdef
  have hp : p ≠ 0 := by
    intro h0
    apply hv
    exact Subtype.ext h0
  have hmem : ∀ x, N *ᵥ x ∈ LinearMap.range N.mulVecLin := fun x =>
    LinearMap.mem_range_self N.mulVecLin x
  choose c hc using fun x => hspan ⟨N *ᵥ x, hmem x⟩
  have hc' : ∀ x, c x • p = N *ᵥ x := fun x => by
    simpa [hpdef] using congrArg Subtype.val (hc x)
  have hadd : ∀ x y, c (x + y) = c x + c y := by
    intro x y
    apply smul_left_injective K hp
    simp only [add_smul]
    rw [hc', hc', hc', mulVec_add]
  have hsmul : ∀ (a : K) x, c (a • x) = a * c x := by
    intro a x
    apply smul_left_injective K hp
    simp only [smul_eq_mul]
    rw [mul_smul, hc', hc', mulVec_smul]
  let f : (Fin n → K) →ₗ[K] K :=
    { toFun := c
      map_add' := hadd
      map_smul' := fun a x => by simpa using hsmul a x }
  obtain ⟨r, hr⟩ := exists_dotProduct_row f
  have hNeq : N = Matrix.vecMulVec p r := by
    refine Matrix.ext_iff_mulVec.mpr fun x => ?_
    rw [vecMulVec_mulVec_smul, ← hc' x]
    have hcx : c x = r ⬝ᵥ x := hr x
    rw [hcx]
  have hr0 : r ≠ 0 := by
    intro hr0
    have hN0 : N = 0 := by rw [hNeq, hr0, Matrix.vecMulVec_zero]
    rw [hN0, Matrix.rank_zero] at h
    exact absurd h (by norm_num)
  have hMeq : M = dihTv p r := by
    unfold dihTv
    rw [← hNeq, hNdef]
    abel
  refine ⟨p, r, hp, hr0, ?_, hMeq⟩
  rw [hMeq, dihTv_det] at hdet
  linear_combination hdet

end DihTv

end CFSG.RankThree.GF2n.Smith81
