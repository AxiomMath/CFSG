module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3KnownForms
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmEntry
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Reduction

theorem ggSixLSixSevenConjA3At_of_known {t : StatedLieTag} (h : GGSixA3ConjKnown t) :
    GGSixLSixSevenConjA3At t := by
  intro G _ _ p B Bs x L D J n f ψ hctx _ _ _ hA
  obtain ⟨hp3, -, -⟩ := hctx.a3_structure ggLNoncyclicInput_holds hA
  subst hp3
  have hrange : ψ.range = ggG0 3 B x L D J := hctx.2.2.2.2.1.1
  have hcen : ¬ 3 ∣ Nat.card (Subgroup.centralizer (ggG0 3 B x L D J : Set G)) :=
    not_dvd_card_centralizer_ggG0_of_stdSub hctx.prime hctx.sstar hctx.stdType hctx.stdSub
  have hDBs : D ≤ Bs := hctx.d_le_bstar
  exact h G n f ψ _ D J hrange hctx.2.2.2.2.1.2 hctx.2.2.2.2.2.1.2 hcen
    (hDBs.trans hctx.2.2.2.2.2.2.1.1) (fun b hb => hctx.2.2.2.2.2.2.1.2 b (hDBs hb))
    hctx.d_elem hctx.card_d hctx.j_isComponentOf_inf hA

theorem ggSixLSixSevenConjA3Round12Rem_of_known (hE6 : GGSixA3ConjKnown .E6)
    (hF4 : GGSixA3ConjKnown .F4) (hTw : GGSixA3ConjKnown .twistedE6) :
    GGSixLSixSevenConjA3Round12Rem :=
  ⟨ggSixLSixSevenConjA3At_of_known hE6, ggSixLSixSevenConjA3At_of_known hF4,
    ggSixLSixSevenConjA3At_of_known hTw⟩

theorem ggSixLSixSevenConjA3Round12Rem_of_knownTags (h : GGSixA3ConjKnownTags) :
    GGSixLSixSevenConjA3Round12Rem :=
  ggSixLSixSevenConjA3Round12Rem_of_known h.1 h.2.1 h.2.2

end Reduction

end CFSG.StandardType
