module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetInputs
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetRow
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetMarking
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetData
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetNoL34
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetCard
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetDecomp
public import CFSG.LocalAnalysis.StandardType.GGR4JNCDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JNCCentre
public import CFSG.LocalAnalysis.StandardType.GGR4JNCCard
public import CFSG.LocalAnalysis.StandardType.GGR4JNCLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggR4JCardNC_of_inputs
    (hAmb : GGR4AmbientLabel) (hM7a : GGF4OrderThreeLayer) (hM7b : GGE6OppOrderThreeLayer)
    (hZtw : GGCentreTrivialTwKnown) (hKG : GGTwTorusAutKnown) : GGR4JCardNC := by
  intro G _ _ p B Bs x L D J hCfg hOp hInnAll hNT y K hnbr hRG hSc hFact hp Λ _ _ C b c V _ _ ι φ'
    h' α' hD hspan hF4 hGenL hGenK
  have hE : 3 ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G) :=
    ggR4JMeet_of_inputs hAmb hM7a hM7b G p B Bs x L D J hCfg hOp hInnAll hNT y K hnbr hRG hSc hp
      Λ C b c V ι φ' h' α' hD hspan hF4 hGenL hGenK
  subst hp
  obtain ⟨e, he, -⟩ := hF4
  have hcardΛ : Fintype.card Λ = 4 := by
    simpa using (Fintype.card_congr e).symm
  have hCard : Nat.card Bs = 3 ^ 5 := ggR4J_card_Bs hD hspan hcardΛ
  have hLab := hAmb G B Bs x L D J hCfg hInnAll.1 hCard Λ C V ι (fun i => φ' (some i))
    (fun i => h' (some i)) (fun i => α' (some i)) (ggExtDatum_restrict_some hD) ⟨e, he⟩ hGenL
  obtain ⟨hperf, hInnL, hZL, f, hf, hrow⟩ :=
    ggR4Meet_marking_of_row ggR4SurvivorRow_holds hLab
  obtain ⟨hJL, z, hz1, hz3, hJlayer, hJcomp, -, -, -⟩ :=
    ggR4Meet_data hCfg hCard hZL hInnL
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hInnAll.1
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hperf
  have hlabJ : GGR4JLabel (↥J ⧸ Subgroup.center ↥J) :=
    ggR4J_label_of_row hM7a hM7b hf hrow hJL hz1 hz3 hJlayer hJcomp
      (fun hL1 hJ1 => ggR4Meet_noE6TwoL34 hCfg hBsN hCard hperf hZL hL1 hJ1)
  refine ⟨fun hnoC => ?_, hlabJ⟩
  obtain ⟨f', hf'⟩ := hlabJ
  have htw : (3 ∣ 2 ^ f' - 1 ∧ GGHasLabel ⟨.twA, 5, f'⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      (3 ∣ 2 ^ f' + 1 ∧ GGHasLabel ⟨.A, 5, f'⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
      GGHasLabel ⟨.twD, 4, f'⟩ (↥J ⧸ Subgroup.center ↥J) := by
    rcases hf' with hC | h | h | h
    · exact absurd hC (hnoC f')
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hBsEA : IsElemAbelian 3 Bs := hCfg.2.1.2.1
  have hSCs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hCfg.2.1.2.2.2
  have hDBs : D ≤ Bs := hCfg.2.2.1.1.trans hCfg.2.1.1
  have hDcard : Nat.card D = 3 ^ 2 := hCfg.2.2.1.2.2.1
  have hDJ : D ≤ Subgroup.centralizer (J : Set G) :=
    (le_of_eq hCfg.2.2.1.2.2.2.2.2.2).trans inf_le_right
  have hJq : CFSG.Assembly.IsQuasisimple J := (hCfg.2.2.1.2.2.2.2.2.1).2.2
  have hJperf : commutator ↥J = ⊤ := hJq.1
  have hZ := ggR4J_center_coprime_tw hZtw hJperf htw
  have hBs : Nat.card Bs ≤ 3 ^ 5 := hCard.le
  have hInnJ := ggR4J_inn_of_meet hBsEA hDBs hDcard hDJ hZ hBs hE
  exact ggR4J_card_ge_tw hKG hBsEA hSCs hJperf hZ hInnJ hE htw

end CFSG.StandardType

end
