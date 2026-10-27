module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneA2
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneD4
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTable

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ntp_compField_normalForm
    (hS : LangNontoralStructure) (hA : LangNontoralA2Descent) (hD : LangNontoralD4Fixed)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (D : Subgroup (ModGL .E6 L))
    (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L) (hnf : ntpNormalForm S D a n)
    (K : Subgroup (ModGL .E6 L))
    (hK : IsComponentOf K (S.Γ ⊓ Subgroup.centralizer (D : Set (ModGL .E6 L)))) :
    GGCompFieldAt S.D.q K ∨
      (S.D.q = 2 ∧ Nat.card K = 6048 ∧
        Nat.card (↥K ⧸ Subgroup.center ↥K) = 6048) := by
  obtain ⟨hpair, hDeq⟩ := OrderThreeOutsideConnected.of_ntpNormalForm hnf
  subst hDeq
  obtain ⟨ha3, _, hda1, _, _, _, C, m, hm, _, _, _, hstab, hnotker⟩ := hpair
  have hpair' : OrderThreeOutsideConnected S a n :=
    (OrderThreeOutsideConnected.of_ntpNormalForm hnf).1
  have ha1 : a ≠ 1 := fun h => hda1 (by rw [h, rootDiagUnit_one])
  rcases e6_three_class_table a ha3 ha1 with hstab_eq | ⟨h18 | h24, -⟩
  · exact absurd (hstab_eq ▸ hstab) hnotker
  · exact Or.inl (ntp_A2 hS hA S a n hpair' h18 K hK)
  · exact ntp_D4 hD S a n hpair' h24 K hK

end CFSG.StandardType.NTPlane

end
