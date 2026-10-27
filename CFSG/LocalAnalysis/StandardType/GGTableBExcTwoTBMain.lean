module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLVac
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLine
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley TableB

namespace TableBExcTwoTB

section Labels


@[expose] def GGE7TwoThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E7 ∧ lab.n = 1 ∧ p = 3

@[expose] def GGE8TwoThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E8 ∧ lab.n = 1 ∧ p = 3

@[expose] def GGE7TwoSCToralInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → GGE7TwoSCToral K

@[expose] def GGE8TwoSCToralInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 → GGE8TwoSCToral K

theorem excLVac_of_e7TwoThree {p : ℕ} {lab : LargeEvenLabel} (h : GGE7TwoThreeLabel p lab) :
    GGExcLVacLabel p lab :=
  ⟨by rw [h.2.2]; norm_num, Or.inr (Or.inl h.1), by rw [h.2.1, h.2.2]; norm_num⟩

theorem excLVac_of_e8TwoThree {p : ℕ} {lab : LargeEvenLabel} (h : GGE8TwoThreeLabel p lab) :
    GGExcLVacLabel p lab :=
  ⟨by rw [h.2.2]; norm_num, Or.inr (Or.inr (Or.inl h.1)), by rw [h.2.1, h.2.2]; norm_num⟩

theorem largeEvenLabelAll_torusIrredSCr_e7TwoThree (hE7 : GGE7TwoSCToralInput) {p : ℕ}
    {lab : LargeEvenLabel} (h : GGE7TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ TwE6TB.GGTorusIrredSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  dsimp only at htag hn
  subst htag
  subst hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 6, TableBExcTwo.ggTorusLift_E7Two,
    ggTorusIrredSCr_E7_two hK (hE7 K hK)⟩

theorem largeEvenLabelAll_torusIrredSCr_e8TwoThree (hE8 : GGE8TwoSCToralInput) {p : ℕ}
    {lab : LargeEvenLabel} (h : GGE8TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ TwE6TB.GGTorusIrredSCr p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  dsimp only at htag hn
  subst htag
  subst hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 7, TableBExcTwo.ggTorusLift_E8Two,
    ggTorusIrredSCr_E8_two hK (hE8 K hK)⟩

theorem ggTableBIrredInputOn_e7TwoThree (hE7 : GGE7TwoSCToralInput) :
    GGTableBIrredInputOn GGE7TwoThreeLabel :=
  TwE6TB.ggTableBIrredInputOn_of_labelsSCr fun _ _ _ _ h =>
    largeEvenLabelAll_torusIrredSCr_e7TwoThree hE7 h

theorem ggBstarInnerDiagLInputOn_e7TwoThree : GGBstarInnerDiagLInputOn GGE7TwoThreeLabel := by
  have h := ggBstarInnerDiagLInputOn_excLVac GGE7TwoThreeLabel
  have e : (fun p lab => GGE7TwoThreeLabel p lab ∧ GGExcLVacLabel p lab) = GGE7TwoThreeLabel :=
    funext fun p => funext fun lab => propext
      ⟨fun h => h.1, fun h => ⟨h, excLVac_of_e7TwoThree h⟩⟩
  rw [e] at h
  exact h

theorem ggTableBCxInputOn_e7TwoThree_holds (hE7 : GGE7TwoSCToralInput) :
    GGTableBCxInputOn GGE7TwoThreeLabel :=
  ggTableBCxInputOn_of_irred ggBstarInnerDiagLInputOn_e7TwoThree
    (ggTableBIrredInputOn_e7TwoThree hE7)

theorem ggTableBModuleInputOn_e7TwoThree_holds (hE7 : GGE7TwoSCToralInput) :
    GGTableBModuleInputOn GGE7TwoThreeLabel :=
  ggTableBModuleInputOn_of_irred ggBstarInnerDiagLInputOn_e7TwoThree
    (ggTableBIrredInputOn_e7TwoThree hE7)

theorem ggTableBActionInputOn_e7TwoThree_holds (hE7 : GGE7TwoSCToralInput) :
    GGTableBActionInputOn GGE7TwoThreeLabel :=
  ggTableBActionInputOn_of_irred ggBstarInnerDiagLInputOn_e7TwoThree
    (ggTableBIrredInputOn_e7TwoThree hE7)

theorem largeEvenLabelAll_noLineSCr_e7TwoThree (hE7 : GGE7TwoSCToralInput) {p : ℕ}
    {lab : LargeEvenLabel} (h : GGE7TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineSCr p r R I := by
  have hp : p.Prime := h.2.2 ▸ Nat.prime_three
  exact (largeEvenLabelAll_torusIrredSCr_e7TwoThree hE7 h).mono fun _ _ _ _ ⟨r, hl, hi⟩ =>
    ⟨r, hl, TwE6TB.ggNoInvariantLineSCr_of_irredSCr hp hi⟩

theorem ggLNoInvariantLineInputOn_e7TwoThree_holds (hE7 : GGE7TwoSCToralInput) :
    GGLNoInvariantLineInputOn GGE7TwoThreeLabel :=
  ggLNoInvariantLineInputOn_of_labelsSCr fun _ _ _ _ h =>
    largeEvenLabelAll_noLineSCr_e7TwoThree hE7 h

theorem ggTableBIrredInputOn_e8TwoThree (hE8 : GGE8TwoSCToralInput) :
    GGTableBIrredInputOn GGE8TwoThreeLabel :=
  TwE6TB.ggTableBIrredInputOn_of_labelsSCr fun _ _ _ _ h =>
    largeEvenLabelAll_torusIrredSCr_e8TwoThree hE8 h

theorem ggBstarInnerDiagLInputOn_e8TwoThree : GGBstarInnerDiagLInputOn GGE8TwoThreeLabel := by
  have h := ggBstarInnerDiagLInputOn_excLVac GGE8TwoThreeLabel
  have e : (fun p lab => GGE8TwoThreeLabel p lab ∧ GGExcLVacLabel p lab) = GGE8TwoThreeLabel :=
    funext fun p => funext fun lab => propext
      ⟨fun h => h.1, fun h => ⟨h, excLVac_of_e8TwoThree h⟩⟩
  rw [e] at h
  exact h

theorem ggTableBCxInputOn_e8TwoThree_holds (hE8 : GGE8TwoSCToralInput) :
    GGTableBCxInputOn GGE8TwoThreeLabel :=
  ggTableBCxInputOn_of_irred ggBstarInnerDiagLInputOn_e8TwoThree
    (ggTableBIrredInputOn_e8TwoThree hE8)

theorem ggTableBModuleInputOn_e8TwoThree_holds (hE8 : GGE8TwoSCToralInput) :
    GGTableBModuleInputOn GGE8TwoThreeLabel :=
  ggTableBModuleInputOn_of_irred ggBstarInnerDiagLInputOn_e8TwoThree
    (ggTableBIrredInputOn_e8TwoThree hE8)

theorem ggTableBActionInputOn_e8TwoThree_holds (hE8 : GGE8TwoSCToralInput) :
    GGTableBActionInputOn GGE8TwoThreeLabel :=
  ggTableBActionInputOn_of_irred ggBstarInnerDiagLInputOn_e8TwoThree
    (ggTableBIrredInputOn_e8TwoThree hE8)

theorem largeEvenLabelAll_noLineSCr_e8TwoThree (hE8 : GGE8TwoSCToralInput) {p : ℕ}
    {lab : LargeEvenLabel} (h : GGE8TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineSCr p r R I := by
  have hp : p.Prime := h.2.2 ▸ Nat.prime_three
  exact (largeEvenLabelAll_torusIrredSCr_e8TwoThree hE8 h).mono fun _ _ _ _ ⟨r, hl, hi⟩ =>
    ⟨r, hl, TwE6TB.ggNoInvariantLineSCr_of_irredSCr hp hi⟩

theorem ggLNoInvariantLineInputOn_e8TwoThree_holds (hE8 : GGE8TwoSCToralInput) :
    GGLNoInvariantLineInputOn GGE8TwoThreeLabel :=
  ggLNoInvariantLineInputOn_of_labelsSCr fun _ _ _ _ h =>
    largeEvenLabelAll_noLineSCr_e8TwoThree hE8 h

theorem ggTableBCxInputOn_of_not_e7TwoThree (hE7 : GGE7TwoSCToralInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGE7TwoThreeLabel p lab) :
    GGTableBCxInputOn S :=
  ((ggTableBCxInputOn_e7TwoThree_holds hE7).or h).mono fun p lab hlab => by
    by_cases hl : GGE7TwoThreeLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBModuleInputOn_of_not_e7TwoThree (hE7 : GGE7TwoSCToralInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGE7TwoThreeLabel p lab) :
    GGTableBModuleInputOn S :=
  ((ggTableBModuleInputOn_e7TwoThree_holds hE7).or h).mono fun p lab hlab => by
    by_cases hl : GGE7TwoThreeLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBActionInputOn_of_not_e7TwoThree (hE7 : GGE7TwoSCToralInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGE7TwoThreeLabel p lab) :
    GGTableBActionInputOn S :=
  ((ggTableBActionInputOn_e7TwoThree_holds hE7).or h).mono fun p lab hlab => by
    by_cases hl : GGE7TwoThreeLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggLNoInvariantLineInputOn_of_not_e7TwoThree (hE7 : GGE7TwoSCToralInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLNoInvariantLineInputOn fun p lab => S p lab ∧ ¬ GGE7TwoThreeLabel p lab) :
    GGLNoInvariantLineInputOn S := by
  have h' := (ggLNoInvariantLineInputOn_e7TwoThree_holds hE7).or h
  intro G _ _ p B Bs x L D J hC hL E hEBs hxE hE
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_) E hEBs hxE hE
  by_cases h1 : GGE7TwoThreeLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

theorem ggTableBCxInputOn_of_not_e8TwoThree (hE8 : GGE8TwoSCToralInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGE8TwoThreeLabel p lab) :
    GGTableBCxInputOn S :=
  ((ggTableBCxInputOn_e8TwoThree_holds hE8).or h).mono fun p lab hlab => by
    by_cases hl : GGE8TwoThreeLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBModuleInputOn_of_not_e8TwoThree (hE8 : GGE8TwoSCToralInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGE8TwoThreeLabel p lab) :
    GGTableBModuleInputOn S :=
  ((ggTableBModuleInputOn_e8TwoThree_holds hE8).or h).mono fun p lab hlab => by
    by_cases hl : GGE8TwoThreeLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBActionInputOn_of_not_e8TwoThree (hE8 : GGE8TwoSCToralInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGE8TwoThreeLabel p lab) :
    GGTableBActionInputOn S :=
  ((ggTableBActionInputOn_e8TwoThree_holds hE8).or h).mono fun p lab hlab => by
    by_cases hl : GGE8TwoThreeLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggLNoInvariantLineInputOn_of_not_e8TwoThree (hE8 : GGE8TwoSCToralInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLNoInvariantLineInputOn fun p lab => S p lab ∧ ¬ GGE8TwoThreeLabel p lab) :
    GGLNoInvariantLineInputOn S := by
  have h' := (ggLNoInvariantLineInputOn_e8TwoThree_holds hE8).or h
  intro G _ _ p B Bs x L D J hC hL E hEBs hxE hE
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_) E hEBs hxE hE
  by_cases h1 : GGE8TwoThreeLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

end Labels

end TableBExcTwoTB

end CFSG.StandardType

end
