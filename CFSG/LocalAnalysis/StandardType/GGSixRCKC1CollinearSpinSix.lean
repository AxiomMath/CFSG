module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearClassical
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearShort
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinMinus

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

theorem rckCollinearVia_POmegaPlus_three
    {g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .POmegaPlus 3 g).D.rank → ℤ}
    (hβ : β ∈ (ggU .POmegaPlus 3 g).D.roots) (hl : GGLongRoot (ggU .POmegaPlus 3 g).D β) :
    RCKCollinearVia (ggU .POmegaPlus 3 g) β := by
  obtain ⟨e, he⟩ := CFSG.StandardType.RCKRP.irgIsoCompat_omegaPlus_three hg
  obtain ⟨γ, hγ, w, hw, -⟩ := he β hβ hl
  have hlγ : GGLongRoot (ggU .PSL 4 g).D γ := by
    rcases hγ.2 with hlong | ⟨⟨hPs, -⟩ | hF, -⟩
    · exact hlong
    · exact absurd hPs (by decide)
    · exact absurd hF (by decide)
  exact rckCollinearVia_of_mulEquiv_conj e w hw (rckCollinearVia_PSL hg hγ.1 hlγ)

theorem rckCollinearVia_POmegaMinus_three
    {g : ℕ} (hg : 1 ≤ g) {β : Fin (ggU .POmegaMinus 3 g).D.rank → ℤ}
    (hβ : β ∈ (ggU .POmegaMinus 3 g).D.roots) (hl : GGLongRoot (ggU .POmegaMinus 3 g).D β) :
    RCKCollinearVia (ggU .POmegaMinus 3 g) β := by
  obtain ⟨e, he⟩ := CFSG.StandardType.RCKRP.irgIsoCompat_omegaMinus_three hg
  obtain ⟨γ, hγ, w, hw, -⟩ := he β hβ hl
  have hlγ : GGLongRoot (ggU .PSU 4 g).D γ := by
    rcases hγ.2 with hlong | ⟨⟨hPs, -⟩ | hF, -⟩
    · exact hlong
    · exact absurd hPs (by decide)
    · exact absurd hF (by decide)
  exact rckCollinearVia_of_mulEquiv_conj e w hw
    (rckCollinearVia_PSU_long hg (le_refl 4) (by decide) hγ.1 hlγ)

end CFSG.StandardType.RCKC1
