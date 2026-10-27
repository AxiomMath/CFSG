module

public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRest
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClAltSix
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem largeEvenLabelAll_simple_of_markedModel
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {P : LargeEvenRawCont}
    (h : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → MarkedModel lab R → P R I F) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard P) := by
  intro Q hQ
  have hor : LargeEvenRawDatum lab fun R _ I F =>
      (Q R I F ∧ IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a) ∨
        (Q R I F ∧ ¬ (IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a)) := by
    refine largeEvenRawDatum_mono (fun R _ I F hq => ?_) hQ
    by_cases hs : IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a
    · exact Or.inl ⟨hq, hs⟩
    · exact Or.inr ⟨hq, hs⟩
  rcases largeEvenRawDatum_or hor with h1 | h2
  · exact largeEvenRawDatum_imp hlab (fun _ _ _ _ hq => hq.2.2)
      (fun R _ I F hq hm => ⟨hq.1, fun hs hna => h R I F hs hna hm⟩) h1
  · exact largeEvenRawDatum_mono
      (fun R _ I F hq => ⟨hq.1, fun hs hna => absurd ⟨hs, hna⟩ hq.2⟩) h2

theorem markChar_eq_two_of_ne {lab : LargeEvenLabel} (h1 : lab.tag ≠ .B2der)
    (h2 : lab.tag ≠ .G2der) : markChar lab = 2 := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  case B2der => exact absurd rfl h1
  case G2der => exact absurd rfl h2
  all_goals rfl

theorem tag_eq_D_of_markTag_eq_POmegaPlus {lab : LargeEvenLabel}
    (h : markTag lab = .POmegaPlus) : lab.tag = .D ∧ lab.rank ≠ 3 := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  case D =>
    refine ⟨rfl, fun h3 => ?_⟩
    change l = 3 at h3
    simp [markTag, h3] at h
  case twD =>
    dsimp only [markTag] at h
    split_ifs at h
  all_goals cases h

theorem ggInnSubsetLabel_of_D {lab : LargeEvenLabel} (h1 : lab.tag = .D) (h3 : lab.rank ≠ 3) :
    GGInnSubsetLabel lab :=
  Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨h1, h3⟩))))

theorem ggInnSubsetLabel_of_G2der {lab : LargeEvenLabel} (h : lab.tag = .G2der) :
    GGInnSubsetLabel lab :=
  Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))

theorem ggMarkedModel_card_b2der {lab : LargeEvenLabel} (ht : lab.tag = .B2der) {R : Type}
    [Group R] (h : MarkedModel lab R) : Nat.card R = 360 := by
  obtain ⟨e⟩ := nonempty_alternatingGroup_of_markedModel_b2der ht h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

section Orders

theorem ggMarkedModel_card_ne_three_sixty {lab : LargeEvenLabel} (ht : lab.tag ≠ .B2der)
    {R : Type} [Group R] (h : MarkedModel lab R) : Nat.card R ≠ 360 := by
  by_cases hg : lab.tag = .G2der
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at hg
    subst hg
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h
    rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
    · rw [Nat.card_congr e.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_three le_rfl hK
          (by norm_num)]
      decide
    all_goals exact absurd hn (by norm_num)
  · have hY := lieModel_of_markedModel (markChar_eq_two_of_ne ht hg) h
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder hY]
    exact ClNonsplit.evenLieOrder_ne_three_sixty_of_admissible
      (CFSG.SeitzReduction.F4Pilot.statedLieAdmissible_of_lieModel hY)

theorem ggInnSubsetLabel_of_markedModel_dFour {lab lab' : LargeEvenLabel} (h1 : lab.tag = .D)
    (h4 : lab.rank = 4) (hb : lab'.tag ≠ .B2der) {X : Type} [Group X] (hM : MarkedModel lab X)
    (hM' : MarkedModel lab' X) : GGInnSubsetLabel lab' := by
  by_cases hg : lab'.tag = .G2der
  · exact ggInnSubsetLabel_of_G2der hg
  obtain ⟨t, l, n⟩ := lab
  dsimp only at h1 h4
  subst h1 h4
  have hX : LieModel X .POmegaPlus 4 2 n := hM
  obtain ⟨hD, h3⟩ := tag_eq_D_of_markTag_eq_POmegaPlus
    (CFSG.SeitzReduction.OmegaPilot.lieModel_POmega_two_unique (Or.inl rfl) hX
      (lieModel_of_markedModel (markChar_eq_two_of_ne hb hg) hM')).1
  exact ggInnSubsetLabel_of_D hD h3

theorem isEmpty_mulEquiv_of_ggExclNoIsoPair {lab lab' : LargeEvenLabel}
    (hP : GGExclNoIsoPair lab lab') {R R' : Type} [Group R] [Group R']
    (hM : MarkedModel lab R) (hM' : MarkedModel lab' R') : IsEmpty (R ≃* R') := by
  refine ⟨fun σ => ?_⟩
  obtain ⟨hX, hS, hB⟩ := hP
  have hcard : Nat.card R = Nat.card R' := Nat.card_congr σ.toEquiv
  by_cases hb : lab.tag = .B2der
  · exact ggMarkedModel_card_ne_three_sixty (fun h => hB ⟨hb, h⟩) hM'
      (hcard.symm.trans (ggMarkedModel_card_b2der hb hM))
  by_cases hb' : lab'.tag = .B2der
  · exact ggMarkedModel_card_ne_three_sixty hb hM (hcard.trans (ggMarkedModel_card_b2der hb' hM'))
  rcases hX with (⟨h1, h4⟩ | h) | (⟨h1, h4⟩ | h)
  · exact hS ⟨ggInnSubsetLabel_of_D h1 (by omega),
      ggInnSubsetLabel_of_markedModel_dFour h1 h4 hb' hM (hM'.of_mulEquiv σ.symm)⟩
  · exact hb h
  · exact hS ⟨ggInnSubsetLabel_of_markedModel_dFour h1 h4 hb hM' (hM.of_mulEquiv σ),
      ggInnSubsetLabel_of_D h1 (by omega)⟩
  · exact hb' h

theorem ggExclNoIsoInput_holds : GGExclNoIsoInput := by
  intro lab hlab
  refine largeEvenLabelAll_simple_of_markedModel hlab fun R _ I F _ _ hM lab' hlab' hP => ?_
  exact largeEvenLabelAll_simple_of_markedModel hlab' fun R' _ _ _ _ _ hM' =>
    isEmpty_mulEquiv_of_ggExclNoIsoPair hP hM hM'

end Orders

theorem ggRawInndiagIsoRound5_holds :
    GGRawInndiagIsoRound5 :=
  ggRawInndiagIsoRound5_of_noIso ggExclNoIsoInput_holds

end CFSG.StandardType
