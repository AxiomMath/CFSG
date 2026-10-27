module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R885Three
public import CFSG.LocalAnalysis.UniquenessCase.OpenThree.S2114K2TU4
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114E3R885
import CFSG.LocalAnalysis.UniquenessCase.OpenThree.R891Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)

variable {G : Type} [Group G] [Finite G]


theorem s21_14K2T_dataOfSetup
    (hGF : CFSG.Yardstones.Me2c15c2c995a.GF2nCatalogClause)
    (hS : Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (hMS : S.InMSigma) :
    S21_14K2T (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
  s21_14K2T_of_r885_r891 CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
    (PartTwo.Three.r885_dataOfSetup hGF hS hUC hC S hMS) (r891_dataOfSetup hS hUC hC S hMS)
    (s21_14K2TU4_dataOfSetup hGF hS hUC hC S hMS)

end CFSG.LocalAnalysis.UniquenessCase.UC22
