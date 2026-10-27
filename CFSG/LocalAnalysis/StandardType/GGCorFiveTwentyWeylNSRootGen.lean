module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeA
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNS
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification TableB

@[expose] def GGHypG0InputNS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDomNS p B Bs x L D J →
        GGHypCompInG0 p B Bs x L D J

@[expose] def GGRootGenLInputNS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDomNS p B Bs x L D J →
        GGRootCompGenAvoiding p Bs L

@[expose] def GGRootGenNbrInputNS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDomNS p B Bs x L D J →
        ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGRootCompGenAvoiding p Bs K

@[expose] def GGHypDichotomyInputNS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDomNS p B Bs x L D J →
        ∀ (t : MulAut ↥Bs) (Jt : Subgroup G), GGIsReflection p t → t ∈ ggInduced Jt Bs →
          Jt ≤ Subgroup.centralizer (ggFixG Bs t : Set G) →
          IsPComponent p (Jt.subgroupOf (Subgroup.centralizer (ggFixG Bs t : Set G))) →
          Jt ≤ ggG0 p B x L D J ∨ ∀ a ∈ ggInduced J Bs, t * a = a * t

@[expose] def GGExcReflInputNS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDomNS p B Bs x L D J →
        ∃ ρ : MulAut ↥Bs, ∀ t : MulAut ↥Bs, GGIsReflection p t → t ∈ ggAutomizer ⊤ Bs →
          (∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t) → t = ρ

@[expose] def GGExcReflTBInputNS : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDomNS p B Bs x L D J →
        ∀ [Fact p.Prime], Nonempty (GGExcReflTBData p Bs L J)

@[expose] def GGRootGenLInputOnNS (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDomNS p B Bs x L D J →
        GGInnerDiagOnLabel S p Bs L → GGRootCompGenAvoiding p Bs L

@[expose] def GGRootGenNbrInputOnNS (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel GGLabQFour p Bs L →
      GGNbrLabelsOk p B Bs x D J → GGCorFiveTwentyWeylDomNS p B Bs x L D J →
        ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGInnerDiagOnLabel S p Bs K →
          GGRootCompGenAvoiding p Bs K

theorem GGExcReflTBInputNS.toWeyl (h : GGExcReflTBInputNS) : GGExcReflTBInput := by
  intro G _ _ p B Bs x L D J hHyp hq hN hW
  exact h G p B Bs x L D J hHyp hq hN hW.toNS

theorem GGRootGenLInputOnNS.toWeyl {S : ℕ → LargeEvenLabel → Prop} (h : GGRootGenLInputOnNS S) :
    GGRootGenLInputOn S :=
  fun G _ _ p B Bs x L D J hHyp hq hN hW hS => h G p B Bs x L D J hHyp hq hN hW.toNS hS

theorem GGRootGenNbrInputOnNS.toWeyl {S : ℕ → LargeEvenLabel → Prop}
    (h : GGRootGenNbrInputOnNS S) : GGRootGenNbrInputOn S :=
  fun G _ _ p B Bs x L D J hHyp hq hN hW y K hnb hS =>
    h G p B Bs x L D J hHyp hq hN hW.toNS y K hnb hS

theorem ggHypDichotomyInputNS_of_lBalance (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) :
    GGHypDichotomyInputNS :=
  fun G _ _ p B Bs x L D J hHyp _ _ _ t Jt hr hind hJC hpc =>
    ggDichotomy_of_hyp hL hP hHyp hr hind hJC hpc

theorem ggHypDichotomyInputNS_of_catalogueSchreier (hS : CatalogueRelativeB.CatalogueSchreier)
    (hP : GGStdSubPrimeInput) : GGHypDichotomyInputNS :=
  ggHypDichotomyInputNS_of_lBalance (ggLBalanceInput_of_catalogueSchreier hS) hP

theorem ggExcReflInputNS_of_tb (hTB : GGExcReflTBInputNS) : GGExcReflInputNS := by
  intro G _ _ p B Bs x L D J hHyp hq hN hW
  have hp : p.Prime := hHyp.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hHyp.1.1.2.2.2.2.2.1.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hJL : ggAutomizer J Bs ≤ ggAutomizer L Bs :=
    ggAutomizer_mono Bs (hHyp.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left)
  obtain ⟨T⟩ := hTB G p B Bs x L D J hHyp hq hN hW
  by_cases hex : ∃ t : MulAut ↥Bs, GGIsReflection p t ∧ t ∈ ggAutomizer ⊤ Bs ∧
      ∀ φ ∈ ggAutNormalClosure L J Bs, t * φ = φ * t
  · obtain ⟨ρ, hρ, hρA, hρc⟩ := hex
    exact ⟨ρ, fun t ht htA htc => T.unique hp2 hHyp.2.2.2.1 hJL ht htA htc hρ hρA hρc⟩
  · exact ⟨1, fun t ht htA htc => absurd ⟨t, ht, htA, htc⟩ hex⟩

theorem ggHypG0InputNS_of_dichotomy (hD : GGHypDichotomyInputNS) (hE : GGExcReflInputNS) :
    GGHypG0InputNS := by
  intro G _ _ p B Bs x L D J hHyp hq hN hW
  obtain ⟨ρ, hρ⟩ := hE G p B Bs x L D J hHyp hq hN hW
  refine ⟨ρ, fun t Jt htρ hr hind hJC hpc => ?_⟩
  by_contra hJt
  refine htρ (hρ t hr ?_ ?_)
  · obtain ⟨g, -, hgN, hg⟩ := hind
    exact mem_ggAutomizer_iff.mpr ⟨g, Subgroup.mem_top g, hgN, hg⟩
  · exact commutes_ggAutNormalClosure_of_not_le hHyp.1.1.2.2.2.2.2.1.1 (le_ggG0_left p B x L D J)
      (hD G p B Bs x L D J hHyp hq hN hW) hr hind hJC hpc hJt

theorem ggRootGenLInputNS_of_typeA (hKG : GGRootGenKGOn GGTypeALabel)
    (hopen : GGRootGenLInputOnNS GGRootGenOpenLabel) : GGRootGenLInputNS := by
  intro G _ _ p B Bs x L D J hHyp hq hNb hW
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hLx : IsSubnormal L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1.2.1
  rcases GGInnerDiagOnLabel.typeA_or hW.2.1 with hA | hO
  swap
  · exact hopen G p B Bs x L D J hHyp hq hNb hW hO
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGLabPhiOneTwo p lab ∧ GGTypeALabel p lab)
    (fun lab hlab hs => hKG p lab hp (ne_two_of_dvd_four_pow_sub_one hlab.1 hs.1) hlab hs.2)
    (fun _ _ _ _ _ _ hP => hP.1) hA
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  have hp2 : p ≠ 2 := ne_two_of_dvd_four_pow_sub_one hlab.1 hs.1
  obtain ⟨hr, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hBsN hlift
  exact ggRootCompGenAvoiding_of_marking hp hp2 hBs hSC hxBs hLx hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hr h3' hW.1 hT

theorem ggRootGenNbrInputNS_of_typeA (hKG : GGRootGenKGOn GGTypeALabel)
    (hopen : GGRootGenNbrInputOnNS GGRootGenOpenLabel) : GGRootGenNbrInputNS := by
  intro G _ _ p B Bs x L D J hHyp hq hNb hW y K hnb
  have hcfg : GGConfig p B Bs x L D J := hHyp.1
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hKy, -⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hcfg.2.2 hnb)
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  rcases GGInnerDiagOnLabel.typeA_or (hW.2.2 y K hnb).2 with hA | hO
  swap
  · exact hopen G p B Bs x L D J hHyp hq hNb hW y K hnb hO
  obtain ⟨hK, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGLabPhiOneTwo p lab ∧ GGTypeALabel p lab)
    (fun lab hlab hs => hKG p lab hp (ne_two_of_dvd_four_pow_sub_one hlab.1 hs.1) hlab hs.2)
    (fun _ _ _ _ _ _ hP => hP.1) hA
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  have hp2 : p ≠ 2 := ne_two_of_dvd_four_pow_sub_one hlab.1 hs.1
  exact ggRootCompGenAvoiding_of_marking hp hp2 hBs hSC hyBs hKy.2.1 hK θ hBsN
    (fun b hb => ggLAut_mem_of_induces K θ hBsN h3 hb)
    (pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hK θ hBsN hlift)
    (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) (hW.2.2 y K hnb).1 hT

theorem ggRootGenLInputNS_of_openOn (hopen : GGRootGenLInputOnNS GGRootGenOpenLabel) :
    GGRootGenLInputNS :=
  ggRootGenLInputNS_of_typeA ggRootGenKGTypeA_holds hopen

theorem ggRootGenNbrInputNS_of_openOn (hopen : GGRootGenNbrInputOnNS GGRootGenOpenLabel) :
    GGRootGenNbrInputNS :=
  ggRootGenNbrInputNS_of_typeA ggRootGenKGTypeA_holds hopen

theorem ggCorFiveTwentyQFourWeylNSInput_of_rootGen (hH : GGHypG0InputNS)
    (hL : GGRootGenLInputNS) (hK : GGRootGenNbrInputNS) : GGCorFiveTwentyQFourWeylNSInput :=
  fun G _ _ p B Bs x L D J hHyp hq hN hW =>
    normalizer_le_normalizer_ggG0 hHyp.1.1.2.2.2.2.2.1.1 (hH G p B Bs x L D J hHyp hq hN hW)
      (hL G p B Bs x L D J hHyp hq hN hW) (hK G p B Bs x L D J hHyp hq hN hW)

theorem ggCorFiveTwentyQFourScalarFailInput_of_weylNS (h : GGCorFiveTwentyQFourWeylNSInput) :
    GGCorFiveTwentyQFourScalarFailInput :=
  fun G _ _ p B Bs x L D J hHyp hq hN hW _ _ => h G p B Bs x L D J hHyp hq hN hW

theorem ggCorFiveTwentyQFourScalarFailInput_of_ns (hS : CatalogueRelativeB.CatalogueSchreier)
    (hP : GGStdSubPrimeInput) (hTB : GGExcReflTBInputNS)
    (hLo : GGRootGenLInputOnNS GGRootGenOpenLabel)
    (hKo : GGRootGenNbrInputOnNS GGRootGenOpenLabel) : GGCorFiveTwentyQFourScalarFailInput :=
  ggCorFiveTwentyQFourScalarFailInput_of_weylNS
    (ggCorFiveTwentyQFourWeylNSInput_of_rootGen
      (ggHypG0InputNS_of_dichotomy (ggHypDichotomyInputNS_of_catalogueSchreier hS hP)
        (ggExcReflInputNS_of_tb hTB))
      (ggRootGenLInputNS_of_openOn hLo) (ggRootGenNbrInputNS_of_openOn hKo))

end CFSG.StandardType
