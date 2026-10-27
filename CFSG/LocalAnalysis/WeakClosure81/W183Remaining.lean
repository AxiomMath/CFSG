module

public import CFSG.LocalAnalysis.WeakClosure81.W183Griess
public import CFSG.LocalAnalysis.WeakClosure81.SzExcl.WrapW18
public import CFSG.LocalAnalysis.WeakClosure81.W183PglMod
public import CFSG.LocalAnalysis.WeakClosure81.W183FourWrap
public import CFSG.LocalAnalysis.WeakClosure81.W183FU
public import CFSG.LocalAnalysis.WeakClosure81.W183FourOdd
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoMain
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoL24
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Main
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Holds
public import CFSG.LocalAnalysis.WeakClosure81.W183FinRows
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Four
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch1413Final
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch210Main
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Odd
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Main
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthHolds
public import CFSG.LocalAnalysis.WeakClosure81.W16LCited
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Main
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5AboveFive
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASFinal
public import CFSG.LocalAnalysis.WeakClosure81.RankThreePrimePowerBounds
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch22One
import CFSG.LocalAnalysis.WeakClosure81.W183Artin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (listBNonabelian)



theorem w3Thm183_of_remaining_inputs
    (hB : Asc80ThmB)
    (hCore : OddTranspositionCoreInputSCCls) (hList : OddTranspListBundleCls)
    (hComp : OddTranspositionCompFactorInput) :
    ∀ (G : Type) [Group G] [Finite G], W3Thm183 G := by
  intro G _ _
  obtain ⟨rows, hL28, hSz8, hGraph, g1syl, g11cov⟩ := w183FinRows asch6_5Four_holds
  have h64o : Asch6_4Odd := asch6_4Odd_holds
  have h64s : Asch6_4Seven := asch6_4Seven_holds
  have h54 : Asch5_4 := asch5_4_holds
  have h210 : Asch2_10 := asch2_10_holds
  have h65o : Asch6_5Odd := asch6_5Odd_holds
  have h1413 : Asch5_14_13Prime := asch5_14_13Prime_holds h64o h64s
  have hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels :=
    CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds
  have hO : LieOrderFormulasInput :=
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have h22 : Asch2_2One :=
    asch2_2One_of_tables hGA
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds
  have b3 : Tail1812Two_AS G :=
    tail1812Two_AS_of_CF hGA hComp hList.toInput orthReflParabolic_holds
      (tail1812TwoNoSectionCF_of_lieOrderFormulas hO artinDistinctOddOrders_holds) hGraph
      (tail1812TwoL24U34_of_inputs h210
        (tail1812FourL24U34_of_masters hO rows h210 (fourU34Two_of_inputs h210 h22)))
  exact w3Thm183_of_branches_AS_free (w3Thm162Gt2_of_cited hB hCore hList) h54
      (asch5_11AS_of_remaining_inputs h54) asch5_12_holds
      (asch5_13AS_of_inputs asch5_12_holds asch4_11ASPow_holds)
      (oddMultiplierSocle185_of_griess hGA)
      CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
      (asch6_6_of_parts (asch6_6Family_of_cited hGA h64o h65o)
          (asch6_6Pgl_of_parts h64s asch6_6PglMod))
      (SzExcl.tail189Two_AS_of_sevenElevenInputs hCore.toInput hList.toInput orthReflParabolic_holds)
      b3
      (tail1812FourFree_AS_of_split
          (tail1812Four_AS_of_masters hGA h1413 hO rows hL28 hSz8 h210 h22
              (fourU34Two_of_inputs h210 h22) (fourOdd_of_inputs h210 h64o h65o) b3)
          (tail1812FourFreeKStar_holds hGA hO listBNonabelian b3
              (Br3Rows.of_br1Rows rows h210 g1syl g11cov)))

end CFSG.LocalAnalysis.WeakClosure81

end
