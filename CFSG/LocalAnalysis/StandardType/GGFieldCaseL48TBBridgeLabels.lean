module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeA
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreExc
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreOrth
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenUnitaryIrred
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreSp
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBHalf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggL48IrredModOrWPlus_covered
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : GGTypeALabel p lab ∨ GGTableBNbrInnerExcSplitLabel p lab ∨ GGTableBF4Label p lab ∨
      GGCorFourTwoOrthSplitLabel p lab ∨ GGE6TwoThreeLabel p lab ∨ GGUnitaryCoprimeLabel p lab ∨
      GGSpNonsplitLabel p lab ∨ GGOrthNsLabel p lab ∨ TableBExcTwoTB.GGE7TwoThreeLabel p lab ∨
      TableBExcTwoTB.GGE8TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableB p R I ∨ GGWPlusTableB p R I := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact largeEvenLabelAll_irredModTableB_of_torusIrred hp
      (TypeA.largeEvenLabelAll_tableBIrred_typeA hp hlab h)
  · exact largeEvenLabelAll_irredModTableB_of_torusIrred hp
      (largeEvenLabelAll_torusIrred_excSplit hp hlab h)
  · exact largeEvenLabelAll_irredModTableB_of_torusIrred hp
      (largeEvenLabelAll_torusIrred_F4 hp hlab h)
  · exact largeEvenLabelAll_irredModTableB_of_torusIrred hp
      (largeEvenLabelAll_torusIrred_orthSplit hp hlab h)
  · exact largeEvenLabelAll_irredModTableB_of_torusIrred hp
      (largeEvenLabelAll_torusIrred_e6TwoThree h)
  · exact (largeEvenLabelAll_torusIrredSC_unitary hp hlab h).mono fun _ _ _ _ hT =>
      Or.inl (ggIrredModTableB_of_torusIrredSC hp hT)
  · exact (largeEvenLabelAll_torusIrredSC_spNonsplit hp hlab h).mono fun _ _ _ _ hT =>
      Or.inl (ggIrredModTableB_of_torusIrredSC hp hT)
  · exact (largeEvenLabelAll_torusIrredSC_orthNs hp h).mono fun _ _ _ _ hT =>
      Or.inl (ggIrredModTableB_of_torusIrredSC hp hT)
  · exact largeEvenLabelAll_irredModTableB_of_torusIrredSCr hp
      (TableBExcTwoTB.largeEvenLabelAll_torusIrredSCr_e7TwoThree
        TableBExcTwoTB.ggE7TwoSCToralInput_holds h)
  · exact largeEvenLabelAll_irredModTableB_of_torusIrredSCr hp
      (TableBExcTwoTB.largeEvenLabelAll_torusIrredSCr_e8TwoThree
        TableBExcTwoTB.ggE8TwoSCToralInput_holds h)

end CFSG.StandardType
end
