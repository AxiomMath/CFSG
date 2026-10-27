module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.StandardType.FF81.CatalogueQ1Defs
public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.Final
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B1Normal
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.CenBOdd
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.FiveOne
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.KFixed
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.KRank
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.KSimple
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Setup
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Data
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4K
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4V2
public import CFSG.RankThree.PartTwo.Sec21.FF79ThmADefs

@[expose] public section

namespace CFSG.StandardType.FF81

open CFSG.Assembly

theorem propOne_of_catalogueQ1 (hQ : CatalogueQ1) : PropOne := by
  intro G _ _ _ hnab _ hK n b L hA z hM hF
  by_contra hno
  push Not at hno
  have h : PropOne.Counterexample G n b L z := ⟨inferInstance, hnab, hA, hM, hF, hno⟩
  obtain ⟨B₂, hB₂⟩ := PropOne.exists_b2Package h (PropOne.b1_normal h) (PropOne.odd_cen h)
  obtain ⟨A, hA'⟩ := PropOne.exists_aStar h hB₂
  obtain ⟨τ, c, hτc⟩ := PropOne.exists_tauC h
  have hS := PropOne.sylowData h hB₂ hA' hτc
  have hT := PropOne.not_sylow_le_cen_b1 h hB₂ hA' hτc hS
  obtain ⟨J, hJ⟩ := PropOne.exists_jData h
  obtain ⟨R, hR⟩ := PropOne.exists_rData h hJ hB₂ hA' hτc hS hT
  obtain ⟨hsimp, hnabK⟩ := PropOne.isSimpleGroup_ksec h hJ hR
  have hrk := PropOne.four_le_pRank_ksec h hJ hR
  obtain ⟨β, hβ3, -, O, J', hfix, hOJ, hcomm, hcop, hmodel⟩ :=
    PropOne.exists_fixed_ksec h hJ hR
  have hcen : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top y) x)
  have hne : PropOne.ktil R ≠ ⊤ := by
    intro htop
    have hle : (⊤ : Subgroup G) ≤ Subgroup.centralizer (R : Set G) :=
      htop ▸ Subgroup.map_subtype_le _
    have hR1 : R ≤ Subgroup.center G := fun r hr =>
      Subgroup.mem_center_iff.mpr fun g =>
        (Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g)) r hr).symm
    rw [hcen] at hR1
    have h9 := hR.card
    rw [le_bot_iff.mp hR1, Subgroup.card_bot] at h9
    omega
  haveI := hsimp
  have hcat : InCatalog (PropOne.Ksec R) :=
    CFSG.ComponentClassification.CatalogueKProper.simple_image_of_surjective G hK
      (PropOne.ktil R) hne (PropOne.Ksec R) (PropOne.ktilHom R) (PropOne.ktilHom_surjective R)
  exact hQ (PropOne.Ksec R) hnabK hcat hrk β hβ3 O J' hfix hOJ hcomm hcop hmodel

theorem propOne_holds :
    PropOne :=
  propOne_of_catalogueQ1 catalogueQ1_holds

end CFSG.StandardType.FF81

end
