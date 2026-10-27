module

public import CFSG.LocalAnalysis.StandardType.GGSuDvdRootGenAsm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNSRootGen
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Main
public import CFSG.LocalAnalysis.StandardType.GGNbrU63

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGRootGenUnitaryDvd63Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∧ p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n ∧ lab.rank = 5 ∧ p = 3

private theorem ggUnitDvd63Label_facts {p : ℕ} {lab : LargeEvenLabel}
    (h : GGRootGenUnitaryDvd63Label p lab) :
    GGUnitDvd63Label p lab ∧ GGNbrInner937U63Label p lab ∧ LargeEvenSplit p lab := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, hpn, -, rfl, rfl⟩ := h
  refine ⟨⟨⟨rfl, by norm_num, hpn, by norm_num⟩, rfl, rfl⟩,
    ⟨⟨rfl, by norm_num, hpn, by norm_num⟩, rfl, rfl⟩, ?_⟩
  exact Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, hpn⟩)

private theorem largeEvenLabelAll_unitDvd63_rootGen
    {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (h : GGRootGenUnitaryDvd63Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusRootGenAvoidKG p 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨rfl, hpn, hn, rfl, rfl⟩ := h
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, hQ',
    ggTorusRootGenAvoidKG_unitaryDvd hK hn (by norm_num) hp hpn (by norm_num) (by norm_num)⟩

theorem ggRootCompGenAvoiding_L_unitaryDvd63
    {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLabel GGRootGenUnitaryDvd63Label p Bs L) :
    GGRootCompGenAvoiding p Bs L := by
  obtain ⟨hp, hBs, hxBs, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hLx : IsSubnormal L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hLc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGRootGenUnitaryDvd63Label p lab)
    (fun lab _ hs => largeEvenLabelAll_unitDvd63_rootGen hp hs)
    (fun _ _ _ _ _ _ hP => hP.1) hL
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, hT⟩ := largeEvenRawDatum_exists hraw
  have hM : GGInnerDiagOnLab GGUnitDvd63Label p Bs L :=
    largeEvenMarking_mono (fun lab R _ I F θ hP =>
      ⟨(ggUnitDvd63Label_facts hP.1).1, (ggUnitDvd63Label_facts hP.1).2.2, hP.2.1,
        hP.2.2⟩) hL
  obtain ⟨hr, h3'⟩ := card_range_ggGamma_unitDvd63 hcfg hM hBsN
  exact ggRootCompGenAvoiding_of_marking_avoidKG hp hp2 hBs hSC hxBs hLx hLc θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hr h3' hT

theorem ggRootCompGenAvoiding_nbr_unitaryDvd63
    (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnb : GGNbr p B x D J y K) (hK : GGInnerDiagOnLabel GGRootGenUnitaryDvd63Label p Bs K) :
    GGRootCompGenAvoiding p Bs K := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hst : LargeEvenStandardType p B x L := hcfg.1.2.2.2.2.2.2.2
  obtain ⟨hKy, -⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hcfg.2.2 hnb)
  have hyBs : y ∈ Bs := hcfg.2.1.1 hnb.1.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hKc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGRootGenUnitaryDvd63Label p lab)
    (fun lab _ hs => largeEvenLabelAll_unitDvd63_rootGen hp hs)
    (fun _ _ _ _ _ _ hP => hP.1) hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, hT⟩ := largeEvenRawDatum_exists hraw
  exact ggRootCompGenAvoiding_of_marking_avoidKG hp hp2 hBs hSC hyBs hKy.2.1 hKc θ hBsN
    (fun b hb => ggLAut_mem_of_induces K θ hBsN h3 hb)
    (ggUnitDvd63NbrRankInput_holds hL hPJ G p B Bs x L D J hcfg y K hnb hBsN
      (GGInnerDiagOnLabel.mono_label (fun lab h => (ggUnitDvd63Label_facts h).2.1) hK))
    (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) hT

end CFSG.StandardType

end
