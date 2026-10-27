module

public import CFSG.LocalAnalysis.StandardType.GGRealKGFiveRows
import CFSG.LocalAnalysis.StandardType.GGKGForkOneDone
import CFSG.LocalAnalysis.StandardType.GGRealKGLinNsRoot
import CFSG.LocalAnalysis.StandardType.GGRealKGSpRoot
import CFSG.LocalAnalysis.StandardType.GGRealKGUSplitRoot
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineTwF4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Subgroup

@[expose] def GGRealClassTag (t : LargeEvenLieTag) : Prop :=
  t = .A ∨ t = .twA ∨ t = .B ∨ t = .C ∨ t = .D ∨ t = .twD

theorem ggRealClassTag_of_labelIso {a b : LargeEvenLabel} (h : GGLabelIso a b)
    (ha : GGRealClassTag a.tag) : GGRealClassTag b.tag := by
  rcases h with rfl | ⟨-, hb, -, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact ha
  · rcases hb with h | h <;> simp [GGRealClassTag, h]
  all_goals rw [h]; simp [GGRealClassTag]

theorem ggRealRootSL2On_five_classical
    : GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGRealClassTag lab.tag := by
  intro p lab hp hlab hl h5
  by_cases hs : LargeEvenSplit p lab
  · exact ggForkRootSL2KGInput_holds p lab hp hlab ⟨h5.1, hs⟩
  obtain ⟨i, hi⟩ := ggKGRow_cover_two hp ⟨h5.1, hl.2.1, hl.2.2⟩
  have row : ∀ {j : GGKGRow},
      (GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel j p lab) → GGKGRowLabel j p lab →
        LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusRootSL2 p r R I :=
    fun h hj => h p lab hp hlab hl ⟨h5.1, hj⟩
  have hT := h5.2
  cases i
  case aNonsplit => exact row ggRealRootSL2On_aNonsplit hi
  case aNonsplitDvd => exact row ggRealRootSL2On_aNonsplitDvd hi
  case uSplit => exact row ggRealRootSL2On_uSplit hi
  case uSplitDvd => exact row ggRealRootSL2On_uSplitDvd hi
  case spNonsplit => exact row ggRealRootSL2On_spNonsplit hi
  case dNonsplit => exact row ggRealRootSL2On_dNonsplit hi
  case e6Nonsplit | e7Nonsplit | e8Nonsplit | f4Nonsplit | twe6Split =>
    exfalso
    have ht := hi.1
    rcases hT with h | h | h | h | h | h <;> rw [ht] at h <;> exact LargeEvenLieTag.noConfusion h
  case small => exact row ggRealRootSL2On_small hi
  case aSplit | aSplitDvd => exact (hs (Or.inl ⟨by rw [hi.1]; exact True.intro, hi.2.1⟩)).elim
  case uNonsplit | uNonsplitDvd =>
    exact (hs (Or.inr (Or.inl ⟨by rw [hi.1]; exact id, by rw [hi.1]; simp, hi.2.1⟩))).elim
  case spSplit =>
    exact (hs (Or.inl ⟨by rcases hi.1 with h | h <;> rw [h] <;> exact True.intro, hi.2⟩)).elim
  case dSplit | e6Split | e7Split | e8Split | f4Split =>
    exact (hs (Or.inl ⟨by rw [hi.1]; exact True.intro, hi.2⟩)).elim
  case twdSplit => exact (hs (Or.inr (Or.inr (Or.inl ⟨Or.inl hi.1, hi.2⟩)))).elim
  case twdNonsplit | twe6Nonsplit =>
    exact (hs (Or.inr (Or.inl ⟨by rw [hi.1]; exact id, by rw [hi.1]; simp, hi.2⟩))).elim

@[expose] def GGReflRealizedQFourInputFiveClassical : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGInnerDiagAll p B Bs x L D J → GGNoTransvection p Bs → 5 ≤ p →
      ∀ X : Subgroup G, (X = L ∨ ∃ y, GGNbr p B x D J y X) →
        GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGRealClassTag lab.tag) p Bs X →
          GGReflRealizedIn p Bs X

theorem ggInnerDiagOnLabel_realRoot_classTag (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {p : ℕ} {Bs X : Subgroup G}
    (hq : ∃ lab₁ : LargeEvenLabel, LargeEvenInLambda2 lab₁ ∧
      GGHasLabel lab₁ (X ⧸ Subgroup.center X) ∧ GGRealClassTag lab₁.tag)
    (hM : GGInnerDiagOnLabel GGRealRootLabel p Bs X) :
    GGInnerDiagOnLabel (fun p lab => GGRealRootLabel p lab ∧ GGRealClassTag lab.tag) p Bs X := by
  obtain ⟨lab₁, hΛ₁, hh₁, hT₁⟩ := hq
  obtain ⟨hX, lab₂, hΛ₂, hraw₂⟩ := hM
  have hh₂ : GGHasLabel lab₂ (X ⧸ Subgroup.center X) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw₂
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hT₂ : GGRealClassTag lab₂.tag :=
    ggRealClassTag_of_labelIso (hRig lab₁ lab₂ _ hΛ₁ hΛ₂ hh₁ hh₂) hT₁
  exact ⟨hX, lab₂, hΛ₂, largeEvenRawDatum_mono
    (fun R _ I F ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, ⟨hP.1, hT₂⟩, hP.2⟩) hraw₂⟩

theorem ggReflRealizedQFourInputFiveClassical_of_rootSL2On
    (hKG : GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGRealClassTag lab.tag)
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) :
    GGReflRealizedQFourInputFiveClassical := by
  intro G _ _ p B Bs x L D J hcfg hInn hNT hp5 X hX hq
  have hq0 : GGInnerDiagOnLabel GGLabQFour p Bs X :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨hl, h2, h3⟩ => ⟨hl.1, h2, h3⟩) hq
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hSC : ∀ g ∈ centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hM : GGInnerDiagOnLabel GGRealRootLabel p Bs X := by
    rcases hX with rfl | ⟨y, hnb⟩
    · have hmarkL := hcfg.1.2.2.2.2.2.2.2.1
      obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hH⟩ := largeEvenMarking_exists_hasLabel hmarkL
      have hlat := ggForkLatticeLabel_of_split' hlab hp5 hH.1
      refine largeEvenMarking_mono ?_ (ggInnerDiagOn_relabel hRig hInn.1 hlab hhas)
      rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
      subst h1
      exact ⟨⟨hp2, hlat.2.1, hlat.2.2⟩, h2, h3⟩
    · rcases ggNbr_latticeLabel_or_seven hRig hraw hiso hcfg hInn hp5 hnb with hM | hM | ⟨-, hA8⟩
      · exact largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨hl, h2, h3⟩ =>
          ⟨⟨hp2, hl.2.1, hl.2.2⟩, h2, h3⟩) hM
      · exfalso
        obtain ⟨lab₁, hΛ₁, hh₁, R₁, _, I₁, F₁, θ₁, h₁⟩ := largeEvenMarking_exists_hasLabel hq0
        obtain ⟨lab₂, hΛ₂, hh₂, R₂, _, I₂, F₂, θ₂, h₂⟩ := largeEvenMarking_exists_hasLabel hM
        exact not_ggLabelIso_fieldTwo (hRig lab₁ lab₂ _ hΛ₁ hΛ₂ hh₁ hh₂) h₁.1 (Or.inl h₂.1.2)
      · exfalso
        obtain ⟨lab₁, hΛ₁, hh₁, R₁, _, I₁, F₁, θ₁, h₁⟩ := largeEvenMarking_exists_hasLabel hq0
        have hΛ₂ : LargeEvenInLambda2 ⟨.A, 8, 1⟩ := by
          refine ⟨le_refl 1, ?_⟩
          dsimp only
          omega
        exact not_ggLabelIso_fieldTwo (hRig lab₁ ⟨.A, 8, 1⟩ _ hΛ₁ hΛ₂ hh₁ hA8) h₁.1 (Or.inr rfl)
  have hTq : ∃ lab₁ : LargeEvenLabel, LargeEvenInLambda2 lab₁ ∧
      GGHasLabel lab₁ (X ⧸ Subgroup.center X) ∧ GGRealClassTag lab₁.tag := by
    obtain ⟨lab₁, hΛ₁, hh₁, R₁, _, I₁, F₁, θ₁, h₁⟩ := largeEvenMarking_exists_hasLabel hq
    exact ⟨lab₁, hΛ₁, hh₁, h₁.1.2⟩
  have hMc := ggInnerDiagOnLabel_realRoot_classTag hRig hTq hM
  obtain ⟨hXc, lab, hlab, hraw'⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGRealRootLabel p lab ∧ GGRealClassTag lab.tag)
    (fun lab hlab hs => hKG p lab hp hlab hs.1 ⟨hp5, hs.2⟩) (fun _ _ _ _ _ _ hP => hP.1) hMc
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw'
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hBsN h3I hb
  rcases hX with rfl | ⟨y, hnb⟩
  · obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hXc θ hBsN hlift
    exact ggReflRealizedIn_of_rootSL2 hp hp2 hBs hSC hNT hXc θ hBsN hBsI hr h3 hT
  · exact ggReflRealizedIn_of_rootSL2 hp hp2 hBs hSC hNT hXc θ hBsN hBsI
      (pow_le_card_range_ggGamma_bstar_of_torusLift hcfg hnb hXc θ hBsN hlift)
      (pow_three_le_card_range_ggGamma_bstar hcfg hnb hBsN) hT

theorem ggReflRealizedQFourInputFiveClassical_holds
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) :
    GGReflRealizedQFourInputFiveClassical :=
  ggReflRealizedQFourInputFiveClassical_of_rootSL2On ggRealRootSL2On_five_classical hRig hraw hiso

end CFSG.StandardType

end
