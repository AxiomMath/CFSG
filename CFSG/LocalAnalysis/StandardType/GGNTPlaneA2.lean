module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneA2Orbit
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneA2Split

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ntp_A2
    (hS : LangNontoralStructure) (hA : LangNontoralA2Descent) {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ : ℕ} (S : LangSetup .E6 L p₀) (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L)
    (hpair : OrderThreeOutsideConnected S a n) (hker : (rootCharKernel a).ncard = 18)
    (K : Subgroup (ModGL .E6 L))
    (hK : IsComponentOf K (S.Γ ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
        Set (ModGL .E6 L)))) :
    GGCompFieldAt S.D.q K := by
  rcases ntpA2_orbitDichotomy hS S a n hpair hker with hfix | hcyc
  · exact ntpA2_split hS S a n hpair hker hfix K hK
  · exact hA L p₀ S a n hpair hker hcyc K hK

end CFSG.StandardType.NTPlane

end
