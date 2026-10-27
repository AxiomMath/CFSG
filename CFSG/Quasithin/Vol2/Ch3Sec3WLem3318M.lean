module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318L
public import CFSG.Quasithin.Vol2.Ch3Sec3WLn2C
public import CFSG.Quasithin.Vol2.Ch3Sec3WLem3318C4Fix
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318I

public section

namespace CFSG.Quasithin.H13.L3318

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L3316 (liftPre liftCore liftCore_le)
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

theorem stmt3_3_18_ofW
    (h14 : Stmt3_3_14) (hGA : CFSG.Open.GriessAllModelsStatement) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) (h12 : Step3_3_12R) (h15 : Step3_3_15R)
    (hC34 : CFSG.Quasithin.C134L32CorrM) (h20 : Stmt3_3_20) : Stmt3_3_18 := by
  intro G _ _ T M L D h n hn he
  obtain ⟨e⟩ := he
  have hab := (Hyp331.vPlus_reduced h.toSetup331).2.1
  have : IsMulCommutative ↥(vPlus L T) := hab.1
  refine ⟨inferInstance, ?_⟩
  rintro ⟨k, hk, hDS⟩
  have hn4 : 4 ≤ n := by omega
  have hn5 : n ≤ 5 := by omega
  obtain ⟨α, Φ, hD⟩ := exists_data h14 hGA h hn4 hn5 e hk hDS
  obtain ⟨α₂, hα₂s, hα₂k⟩ := hD.exists_modO2Surj_three
  rcases Ln2.isMSPair_or h hD.mem_lFamilyOf_three (hD.le_normalizer_Y {3}) hα₂s hα₂k with
    hMS | hO
  · have hcomp := cComp_of_isLocal hD.mem_lFamilyOf_three.2
    obtain ⟨i, hi⟩ := Ln2.exists_isC134CaseW hC34 hMS hcomp (hD.le_normalizer_Y {3}) hα₂s hα₂k
    rcases i with _ | _ | _ | _ | _ | _ | i
    · exact hi.elim
    · exact hD.not_case1 hi
    · obtain ⟨rfl, rfl, hQW⟩ := hD.case2 hi
      exact hD.false_of_case2 h38 h39 h12 hQW
    · exact hD.not_case3 hi
    · exact hD.not_case4CorrW h38 h39 h14 h15 h20 hC34 hMS hcomp ⟨hα₂s, hα₂k⟩ hi
    · exact hD.not_case5 h38 h39 hi
    · exact hi.elim
  · exact hD.false_of_pCoreOf_ne_bot h15 hO

end CFSG.Quasithin.H13.L3318
