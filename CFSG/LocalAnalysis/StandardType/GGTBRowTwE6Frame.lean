module

public import CFSG.LocalAnalysis.StandardType.GGTBRowExcFrame
public import CFSG.LocalAnalysis.StandardType.GGTBRowE6Equiv
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6Parity
public import CFSG.LocalAnalysis.StandardType.GGTBRowFrame
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6Plus
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
public import CFSG.LocalAnalysis.StandardType.GGTBRowTwE6FrameAux
public import Certificates.Certificate13657
public import Certificates.Certificate3951

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTwE6Row_frame
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {Rest : Prop} (hHyp : GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧
      GGInnerDiagAll p B Bs x L D J ∧ GGNoTransvection p Bs ∧ Rest)
    (hL : GGInnerDiagOnLabel GGTBTwE6PlusLabel p Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    GGWeylFrame p (ggGamma L hN).range CoxeterMatrix.E₆ := by
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := GGTBTwE6PlusLabel p)
    (fun lab hlab hs => ggTwE6Row_labelAllGuard_frame hp hp2 hlab hs)
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, hlift, hT⟩ :=
    largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces L θ hBsN h3I hb
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
  exact hT L (ggQuotHom θ) _
    (ggTorusTBGroup_of_marking hp hBs hSC hXc θ hBsN hBsI hr h3)

end CFSG.StandardType

end

