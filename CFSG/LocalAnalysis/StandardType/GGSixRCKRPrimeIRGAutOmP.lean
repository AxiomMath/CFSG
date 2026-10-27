module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutOmPAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem irgRootPairAut_POmegaPlus
    {n g : ℕ} (hn : 5 ≤ n) (hadm : StatedLieAdmissible .POmegaPlus n 2 g) :
    IRGRootPairAut .POmegaPlus n g := by
  have hn3 : 3 ≤ n := by omega
  have hsrc : ggU .POmegaPlus n g =
      (⟨spinGroup (Spin.quadPlus n (GaloisField 2 g)),
        Spin.plusDatum n (GaloisField 2 g) hn3⟩ : LieUniversal) := by
    simp only [ggU, lieUniversal, hn3, ↓reduceDIte]
  unfold IRGRootPairAut IRGQuot IRGGoodRoot
  exact irgOP_pairAut_of_eq (ggU .POmegaPlus n g) hn hn3 hsrc

end CFSG.StandardType.RCKRP
