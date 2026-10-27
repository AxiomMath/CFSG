module

public import CFSG.LocalAnalysis.StandardType.GGRealNbrNSTwE6Defs
import CFSG.LocalAnalysis.StandardType.GGRealKGThree
import CFSG.LocalAnalysis.StandardType.GGRealKGThreeUDvd
import CFSG.LocalAnalysis.StandardType.GGRealKGThreeU63
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeAssembly
import CFSG.LocalAnalysis.StandardType.GGRealKGExcNegRows
import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenKG
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private theorem ggRealKGThreeRow_of_ne (i : GGKGRow) (hU : i ≠ .uNonsplitDvd)
    (h6 : i ≠ .twe6Nonsplit) : GGRealKGThreeRow i := by
  cases i
  case aSplit => exact ggRealKGThreeRow_aSplit
  case aSplitDvd => exact ggRealKGThreeRow_aSplitDvd
  case aNonsplit => exact ggRealKGThreeRow_aNonsplit
  case aNonsplitDvd => exact ggRealKGThreeRow_aNonsplitDvd
  case uSplit => exact ggRealKGThreeRow_uSplit
  case uSplitDvd => exact ggRealKGThreeRow_uSplitDvd
  case uNonsplit => exact ggRealKGThreeRow_uNonsplit
  case uNonsplitDvd => exact (hU rfl).elim
  case spSplit => exact ggRealKGThreeRow_spSplit
  case spNonsplit => exact ggRealKGThreeRow_spNonsplit
  case dSplit => exact ggRealKGThreeRow_dSplit
  case dNonsplit => exact ggRealKGThreeRow_dNonsplit
  case twdSplit => exact ggRealKGThreeRow_twdSplit_of_uSplit ggRealKGThreeRow_uSplit
  case twdNonsplit => exact ggRealKGThreeRow_twdNonsplit
  case e6Split => exact ggRealKGThreeRow_e6Split
  case e6Nonsplit => exact ggRealKGThreeRow_e6Nonsplit
  case e7Split => exact ggRealKGThreeRow_e7Split
  case e7Nonsplit => exact ggRealKGThreeRow_e7Nonsplit
  case e8Split => exact ggRealKGThreeRow_e8Split
  case e8Nonsplit => exact ggRealKGThreeRow_e8Nonsplit
  case f4Split => exact ggRealKGThreeRow_f4Split
  case f4Nonsplit => exact ggRealKGThreeRow_f4Nonsplit
  case twe6Split => exact ggRealKGThreeRow_twe6Split
  case twe6Nonsplit => exact (h6 rfl).elim
  case small => exact ggRealKGThreeRow_small

theorem ggRealRootSL2On_three_offU63_offTwE6 :
    GGRealRootSL2On fun p lab =>
      p = 3 ∧ ¬ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) ∧ ¬ GGNbrInner937U63Label p lab := by
  intro p lab hp hlab hl ⟨h3, h6, hU⟩
  subst h3
  by_cases hs : GGTypeALabel 3 lab
  · exact ggRealRootSL2On_typeA 3 lab hp hlab hl hs
  obtain ⟨i, hi⟩ := ggKGRow_cover_three lab
  by_cases hiU : i = .uNonsplitDvd
  · subst hiU
    have h5 : lab.rank ≠ 5 := fun h5 => hU ⟨⟨hi.1, by omega, hi.2.1, hi.2.2⟩, h5, rfl⟩
    exact ggRealRootSL2On_three_uNonsplitDvd_ne_five 3 lab hp hlab hl ⟨rfl, hi, h5⟩
  by_cases hi6 : i = .twe6Nonsplit
  · subst hi6
    exact (h6 hi).elim
  · exact ggRealKGThreeRow_of_ne i hiU hi6 3 lab hp hlab hl ⟨rfl, hi, hs⟩

theorem ggReflRealizedQFourNbrNSInput_of_twE6 (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (h : GGReflRealizedQFourNbrNSTwE6Input) : GGReflRealizedQFourNbrNSInput := by
  intro G _ _ B Bs x L D J 𝒦 hcfg hL y K hnb hnsK hq
  have hc : GGConfig 3 B Bs x L D J := hcfg.1.1
  have hNT : GGNoTransvection 3 Bs := hcfg.1.2.2.2.1
  have hX : K = L ∨ ∃ y, GGNbr 3 B x D J y K := Or.inr ⟨y, hnb⟩
  have h3 : GGInnerDiagOnLabel (fun p lab =>
      (GGLabQFour p lab ∧ lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) ∨
      ((GGLabQFour p lab ∧ GGNbrInner937U63Label p lab) ∨
        (GGLabQFour p lab ∧
          (¬ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) ∧ ¬ GGNbrInner937U63Label p lab)))) 3 Bs K :=
    GGInnerDiagOnLabel.mono_label (fun lab hl => by
      by_cases h6 : lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1
      · exact Or.inl ⟨hl, h6⟩
      · by_cases hU : GGNbrInner937U63Label 3 lab
        · exact Or.inr (Or.inl ⟨hl, hU⟩)
        · exact Or.inr (Or.inr ⟨hl, h6, hU⟩)) hq
  rcases h3.elim_or with h₁ | h₂
  · exact h G B Bs x L D J 𝒦 hcfg hL y K hnb hnsK h₁
  rcases h₂.elim_or with h₂ | h₃
  · exact ggReflRealizedIn_three_U63 hLB hSP hc hNT rfl hX h₂
  · exact ggReflRealizedIn_three_of_rootSL2On
      (S := fun p lab => ¬ (lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) ∧ ¬ GGNbrInner937U63Label p lab)
      ggRealRootSL2On_three_offU63_offTwE6 hc hNT rfl hX h₃

theorem ggReflRealizedIn_three_twE6Nbr (hR : GGTwE6ThreeNbrRankInput) (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hNT : GGNoTransvection 3 Bs) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hInnK : GGInnerDiagOn Bs K)
    (hq : GGInnerDiagOnLabel
      (fun p lab => GGLabQFour p lab ∧ lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) 3 Bs K) :
    GGReflRealizedIn 3 Bs K := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨hXc, lab, hlab, hraw'⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGLabQFour 3 lab ∧ lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (P' := fun R _ I _ => GGTorusRootSL2 3 5 R I)
    (fun lab _ hs => TwE6Delta.labelAll (Q := fun R _ I => GGTorusRootSL2 3 5 R I) hs.2.1
      (fun K _ _ hK => TwE6ThreeRootGen.ggTorusRootSL2_recipeR_twE6Three hs.1 hK hs.2.2))
    (fun _ _ _ _ _ _ hP => hP.1) hq
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, hT⟩ := largeEvenRawDatum_exists hraw'
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces K θ hBsN h3I hb
  have hbad : LargeEvenMarking ↥K fun lab _ _ _ _ _ => GGTwE6BadLabel 3 lab :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2.1, rfl, hP.1.2.2⟩) hq
  have hInnL := ggInnerDiagOnLab_of_twE6BadMarking hRig hInnK hbad
  have hr : 3 ^ 5 ≤ Nat.card ↥(ggGamma K hBsN).range :=
    hR G 3 B Bs x L D J hcfg rfl y K hnb hInnL hBsN (ggTorusSelfCent_ggGamma hBsN hSC)
  exact ggReflRealizedIn_of_rootSL2 hp hp2 hBs hSC hNT hXc θ hBsN hBsI hr
    (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) hT

theorem ggReflRealizedQFourNbrNSTwE6Input_of_rank (hR : GGTwE6ThreeNbrRankInput)
    (hRig : GGLabelRigidInput) : GGReflRealizedQFourNbrNSTwE6Input := by
  intro G _ _ B Bs x L D J 𝒦 hcfg _ y K hnb _ hq
  exact ggReflRealizedIn_three_twE6Nbr hR hRig hcfg.1.1 hcfg.1.2.2.2.1 hnb
    (hcfg.1.2.2.1.2 y K hnb) hq

theorem ggReflRealizedQFourNbrNSInput_of_rank (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hR : GGTwE6ThreeNbrRankInput) (hRig : GGLabelRigidInput) :
    GGReflRealizedQFourNbrNSInput :=
  ggReflRealizedQFourNbrNSInput_of_twE6 hLB hSP (ggReflRealizedQFourNbrNSTwE6Input_of_rank hR hRig)

end CFSG.StandardType

end
