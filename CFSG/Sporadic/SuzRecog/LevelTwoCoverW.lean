module

public import CFSG.Sporadic.SuzRecog.LevelTwoGroups
public import Certificates.Certificate15116

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.LevelTwo

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Sporadic.SuzOddCore
  CFSG.ComponentClassification.AS81.SuzB0

@[expose] def wC : Equiv.Perm (Fin 1782) := invInnerGen 1 3 * invInnerGen 1 6

theorem invInnerGenArrs_one_size : (invInnerGenArrs 1).size = 10 := by
  simp [invInnerGenArrs, invInnerGenCounts]

theorem rep_innerGen_one {j : ℕ} (hj : j < 10) :
    Rep 1782 (invInnerGenArrs 1)[j]! (invInnerGen 1 j) ∧
      Rep 1782 (invCand 1782 (invInnerGenArrs 1)[j]!) (invInnerGen 1 j)⁻¹ := by
  have hj' : j < (invInnerGenArrs 1).size := by rw [invInnerGenArrs_one_size]; exact hj
  have hk : invInnerStart 1 + j < invRunCount 1 := by
    have : j < invInnerGenCounts.getD 1 0 := by simpa [invInnerGenArrs] using hj'
    have h2 := invRunCount_ge 1
    simp only [invOddStart] at h2
    omega
  have h := invRun_inv (by norm_num : 1 < 4) hk
  rw [← invInnerGenArrs_get hj'] at h
  exact rep_permC h

theorem innerGen_one_mem {j : ℕ} (hj : j < 10) :
    invInnerGen 1 j ∈ invE 1 := by
  have hj' : j < (invInnerChain 1).originalCount := by
    show j < (invInnerGenArrs 1).size
    rw [invInnerGenArrs_one_size]
    exact hj
  have hrep := (invInnerChain_arrays (by norm_num : 1 < 4)).orig ⟨j, hj'⟩
  rw [(rep_innerGen_one hj).1.unique hrep]
  exact Subgroup.subset_closure (schreier_vector_get_mem_toList _ _)

theorem wC_mem : wC ∈ invE 1 :=
  mul_mem (innerGen_one_mem (by norm_num)) (innerGen_one_mem (by norm_num))

theorem w_eq_conj :
    suzInv 1 * aP p1 = wC * qVec 1 * wC⁻¹ := by
  obtain ⟨h3, h3i⟩ := rep_innerGen_one (j := 3) (by norm_num)
  obtain ⟨h6, h6i⟩ := rep_innerGen_one (j := 6) (by norm_num)
  have hc : Rep 1782 WCheck.wConjArr (wC * qVec 1 * wC⁻¹) := by
    have := rep_compA h3 (rep_compA h6 (rep_compA (rep_qProd 1) (rep_compA h6i h3i)))
    unfold WCheck.wConjArr WCheck.c3Arr WCheck.c6Arr
    convert this using 1
    unfold wC
    group
  exact eq_of_eqA (rep_compA rep_t1 (rep_aP p1_lt_2835)) hc Certificates.certificate15116

end CFSG.Sporadic.SuzRecog.LevelTwo
