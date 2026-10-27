module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSUAux
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSURoot
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutPSUAssemblyAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem irgRootPairAut_PSU
    {n g : ℕ} (hadm : StatedLieAdmissible .PSU n 2 g) : IRGRootPairAut .PSU n g := by
  have hf : 1 ≤ g := hadm.2.1
  have hK : Nat.card (irgU_F g) = (2 ^ g) ^ 2 := by
    simpa [irgU_F] using card_galoisField_two_mul 2 g hf
  have hsrc : ggU .PSU n g =
      (⟨Unitary.SU (irgU_sigma g) n,
        Unitary.rootDatum (p := 2) (f := g) hK n⟩ : LieUniversal) := by
    simp only [ggU, lieUniversal, hf, ↓reduceDIte, irgU_sigma, irgU_F]
  unfold IRGRootPairAut IRGQuot IRGGoodRoot
  exact irgUM_pairAut_of_eq hK hadm (ggU .PSU n g) hsrc

end CFSG.StandardType.RCKRP
