module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutOmMAux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem irgRootPairAut_POmegaMinus
    {n g : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n 2 g) :
    IRGRootPairAut .POmegaMinus n g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hg1, hn4⟩ := hadm
  have hcard : Nat.card (GaloisField 2 g) = 2 ^ g := GaloisField.card 2 g (by omega)
  have hirr := minusCoeffs_irr 2 g
  intro θ β' hβ' hlong u'
  obtain ⟨u, h1, h2⟩ := irgOM_pairAut_minus hn4 hirr hcard θ hβ' hlong u'
  exact ⟨β', ⟨hβ', Or.inl hlong⟩, u, h1, h2⟩

end CFSG.StandardType.RCKRP
