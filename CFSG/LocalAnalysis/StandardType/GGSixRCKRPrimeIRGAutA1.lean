module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGA1Sl2
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGAutA1Aux

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem irgRootPairAut_PSL_two
    {g : ℕ} (hadm : StatedLieAdmissible .PSL 2 2 g) : IRGRootPairAut .PSL 2 g := by
  intro θ β' hβ' hlong u'
  have hg : 2 ≤ g := by
    rcases hadm with ⟨-, hg1, -, hne, -⟩
    by_contra h
    have h1 : g = 1 := by omega
    exact hne (by rw [h1]; norm_num)
  have hF : 4 ≤ Nat.card (GaloisField 2 g) := by
    rw [GaloisField.card 2 g (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  obtain ⟨β, hβ, hlongβ, u, hmain, hneg⟩ :=
    irgA1_rootPairAut_sl2 (F := GaloisField 2 g) hF θ hβ' u'
  exact ⟨β, ⟨hβ, Or.inl hlongβ⟩, u, hmain, hneg⟩

end CFSG.StandardType.RCKRP
