module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneInput
public import CFSG.LocalAnalysis.StandardType.GGCompFieldLieModel

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ntp_D4
    (hD : LangNontoralD4Fixed) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L)
    (hpair : OrderThreeOutsideConnected S a n) (hker : (rootCharKernel a).ncard = 24)
    (K : Subgroup (ModGL .E6 L))
    (hK : IsComponentOf K (S.Γ ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
        Set (ModGL .E6 L)))) :
    GGCompFieldAt S.D.q K ∨
      (S.D.q = 2 ∧ Nat.card K = 6048 ∧
        Nat.card (↥K ⧸ Subgroup.center ↥K) = 6048) := by
  obtain ⟨hbig, hq2⟩ := hD L p₀ S a n hpair hker K hK
  by_cases h2 : S.D.q = 2
  · exact Or.inr ⟨h2, (hq2 h2).1, (hq2 h2).2⟩
  · obtain ⟨f, hf, hLie⟩ := hbig h2
    have hfield : GGCompFieldAt (2 ^ f) K := by
      rcases hLie with hLie | hLie | hLie <;>
        exact ggCompFieldAt_of_lieModel hK.2.2 hLie (by decide)
    rw [hf] at hfield
    exact Or.inl hfield

end CFSG.StandardType.NTPlane

end
