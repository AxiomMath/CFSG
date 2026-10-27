module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoA5Inputs
public import CFSG.Quasithin.Recognition.L34AmalgamIsoCertInputs
public import Certificates.Data.K426J3
public import CFSG.Certificates.Kernel.CosetW.Sound
import Certificates.Kernel.CosetW.A5
import Certificates.Kernel.CosetW.J3Lift
import Certificates.Kernel.CosetW.L34Bad
import Certificates.Kernel.CosetW.L34Good
import Certificates.Kernel.CosetW.L34P1
import Certificates.Kernel.CosetW.IsoP1
import Certificates.Kernel.CosetW.IsoP2

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.L34Amalgam CFSG.CosetTable
open CFSG.Certificates.CosetEnumeration CFSG.RankThree.PartTwo.KFacts.K426

namespace CertificateChecks.CosetW

theorem proof7038 : subsetCheck a5Rels [] 100000 60 = true := by
  rw [subsetCheck_eq_checkW _ _ (by norm_num)]
  exact a5_checkW

theorem proof8059 : cyclicCheckC j3tLiftRels [2] 4 2000 90 = true := by
  rw [cyclicCheckC_eq_checkW _ _ (by norm_num), j3tLift_checkW]
  decide +kernel

theorem proof7078 : subsetCheck relsP1 [] 100000 960 = true ∧
    subsetCheck relsP2 [] 100000 960 = true := by
  rw [subsetCheck_eq_checkW _ _ (by norm_num), subsetCheck_eq_checkW _ _ (by norm_num)]
  exact ⟨isoP1_checkW, isoP2_checkW⟩

theorem extra_eq_flatten (i : Fin 12) :
    ∀ k, extra i k = (List.replicate k (word "s" ++ word (repStr i))).flatten
  | 0 => by simp [extra, word]
  | k + 1 => by rw [extra_succ, extra_eq_flatten i k, List.replicate_succ, List.flatten_cons]

theorem proof7025 :
    (∀ i : Fin 12, ∀ k ∈ [2, 3], ¬ (IsGood i ∧ k = 3) →
       subsetCheck (relsOf i k) [0, 1, 2, 3] 100000 1 = true)
    ∧ (∀ i : Fin 12, IsGood i →
       subsetCheck (relsOf i 3) [0, 1, 2, 3] 100000 21 = true)
    ∧ (∀ i : Fin 12, IsGood i →
       subsetCheck (restrictWords (subsetOf 5 [0, 1, 2, 3]) (relsOf i 3)) [] 100000 960 =
         true) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i k hk hng
    rw [subsetCheck_eq_checkW _ _ (by norm_num), relsOf, extra_eq_flatten]
    have ha := l34Bad_checkW_a
    have hb := l34Bad_checkW_b
    have hc := l34Bad_checkW_c
    unfold l34BadCheck at ha hb hc
    have h : ((List.finRange 12).all fun i => [2, 3].all fun k =>
        (decide (IsGood i) && k == 3) ||
          checkW (mkParamsW (2 * 5) (invArrW 5)
            (codes (amalRels ++ [(List.replicate k (word "s" ++ word (repStr i))).flatten]))
            (codes ((subsetOf 5 [0, 1, 2, 3]).map fun x => [(x, true)]))) 100000 1) = true := by
      rw [show List.finRange 12 = [0, 1, 2, 3] ++ [4, 5, 6, 7] ++ [8, 9, 10, 11] by decide,
        List.all_append, List.all_append, ha, hb, hc]
      rfl
    simp only [List.all_eq_true, List.mem_finRange, true_implies] at h
    have h' := h i k hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
    exact h'.resolve_left hng
  · intro i hi
    rw [subsetCheck_eq_checkW _ _ (by norm_num), relsOf, extra_eq_flatten]
    rcases hi with rfl | rfl | rfl
    · exact l34Good2_checkW
    · exact l34Good5_checkW
    · exact l34Good7_checkW
  · intro i hi
    have hr : restrictWords (subsetOf 5 [0, 1, 2, 3]) (relsOf i 3) =
        restrictWords (subsetOf 5 [0, 1, 2, 3]) amalRels := by
      have h := l34Extra_restrict
      simp only [List.all_eq_true] at h
      have hi' : i ∈ ([2, 5, 7] : List (Fin 12)) := by
        rcases hi with rfl | rfl | rfl <;> decide
      have he := h i hi'
      rw [restrictWords, List.isEmpty_iff] at he
      rw [relsOf, extra_eq_flatten, restrictWords, restrictWords, List.filterMap_append, he,
        List.append_nil]
    rw [hr, subsetCheck_eq_checkW _ _ (by rw [l34Subset_length]; norm_num)]
    exact l34P1_checkW

end CertificateChecks.CosetW
