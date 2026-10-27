module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2MainB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.FourDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Table
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Fi23
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Fi24
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4M
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Z3
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Type
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Alt
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Odd
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Spor
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Holds
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Main
import CFSG.LocalAnalysis.WeakClosure81.W115Weak
import CFSG.LocalAnalysis.WeakClosure81.W116Weak
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.GH74.GLS (InChev2)
open scoped commutatorElement Pointwise

theorem w135_atChev2_of_chev2 (hC2 : W4Lem13_5Chev2) : W4Lem13_5AtChev2 := by
  intro W _ _ hW Y L t hctx htY ht2 hm hI
  by_cases hz : Subgroup.center ↥L ≠ ⊥ ∧ IsAlt (↥L ⧸ Subgroup.center ↥L) 6
  · obtain ⟨hZ, ⟨e⟩⟩ := hz
    exact W4Lem13_5Concl.of_hatA6
      (GF2Reps13Alt.isHat_alt6_of_is135Context hW hctx htY ht2 hm hZ e)
  · exact hC2 W hW Y L t hctx htY ht2 hm hI (fun hZ h6 => hz ⟨hZ, h6⟩)

theorem w4Lem13_5_of_inputs
    (h105 : W4Lem10_5Four) (hfin : W4Lem10_7Fin) : W4Lem13_5 := by
  have hAt := w135_atChev2_of_chev2 w4Lem13_5Chev2_holds
  refine w4Lem13_5_iff_concl.mpr ?_
  intro W _ _ hW Y L t hctx htY ht2 hm
  rcases w135_typePartition CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge hctx with
      hAlt | hOdd | hEven | hSpor
  · by_cases hZ : Subgroup.center ↥L = ⊥
    · exact w135_alt_case w4Lem8_6_holds hAt hW hctx htY ht2 hm hZ hAlt
    · obtain ⟨n, -, ⟨e⟩⟩ := hAlt
      exact W4Lem13_5Concl.of_hatA6
        (GF2Reps13Alt.isHat_alt6_of_is135Context hW hctx htY ht2 hm hZ e)
  · exact w135_odd_case hAt h105 (w4Lem10_7Irr_of_fin hfin) hW hctx htY ht2 hm hOdd
  · exact hAt W hW Y L t hctx htY ht2 hm (Or.inl hEven)
  · exact w135_spor_case (W4Row.w4Thm11_1RowM4_table_of_five
      (W4Row.w4Thm11_1RowM4_Fi22_of_centre_three W4Row.w4Fi22RowM4CentreThree_holds)
      W4Row.w4Thm11_1RowM4_Fi23_holds W4Row.w4Thm11_1RowM4_Fi24Prime_holds
      W4Row.w4Thm11_1RowM4_B_holds W4Row.w4Thm11_1RowM4_M_holds) W115.w4Lem11_5Weak_holds
      W115.w4Lem11_6Weak_holds hW hctx htY ht2 hm hSpor

end CFSG.LocalAnalysis.WeakClosure81
