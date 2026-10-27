module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoTBSec
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLVac
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLine

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGE6TwoThreeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ lab.n = 1 ∧ p = 3

theorem ggNoInvariantLineSCr_of_ggTorusIrred {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : GGTorusIrred p r R I) : GGNoInvariantLineSCr p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 _
  obtain ⟨W, hW1, hW2, -, -⟩ := h L' ψ hψ hker hperf A hA hAI hr h3
  refine ⟨W, hW1, fun Λ hΛ hΛp => ?_⟩
  by_contra hcon
  push Not at hcon
  rcases hW2 Λ hΛ hcon with hbot | htop
  · rw [hbot, Subgroup.card_bot] at hΛp
    exact hp.one_lt.ne' hΛp.symm
  · rw [htop] at hΛp
    have h1 : p < p ^ 3 := by
      have := Nat.pow_lt_pow_right hp.one_lt (by norm_num : 1 < 3)
      simpa using this
    omega

section Label


theorem largeEvenLabelAll_torusIrred_e6TwoThree {p : ℕ} {lab : LargeEvenLabel}
    (h : GGE6TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusIrred p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  dsimp only at htag hn
  subst htag
  subst hn
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa only [pow_one] using hK
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ', 4, TableBExc.E6Three.ggTorusLift_E6_two,
    E6TwoTB.ggTorusIrred_E6_two hK2⟩

theorem largeEvenLabelAll_pow_mem_e6TwoThree {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGE6TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn, rfl⟩ := h
  have hn1 : 1 ≤ n := hlab.1
  dsimp only at htag hn hn1
  subst htag
  subst hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  exact recipeChevalley_and (fun K _ _ hK => ExcSplitL.mem_chevID_E6_of_pow hn1 K hK hp
    (by norm_num) (by norm_num)) hQ

theorem ggBstarInnerDiagLInputOn_e6TwoThree : GGBstarInnerDiagLInputOn GGE6TwoThreeLabel :=
  CorFourTwoOpen.ggBstarInnerDiagLInputOn_of_pow ggLNoncyclicInput_holds
    fun _ _ hp hlab h => largeEvenLabelAll_pow_mem_e6TwoThree hp hlab h

theorem ggTableBIrredInputOn_e6TwoThree : GGTableBIrredInputOn GGE6TwoThreeLabel :=
  ggTableBIrredInputOn_of_labels fun _ _ _ _ h => largeEvenLabelAll_torusIrred_e6TwoThree h

theorem ggTableBCxInputOn_e6TwoThree_holds : GGTableBCxInputOn GGE6TwoThreeLabel :=
  ggTableBCxInputOn_of_irred ggBstarInnerDiagLInputOn_e6TwoThree ggTableBIrredInputOn_e6TwoThree

theorem ggTableBModuleInputOn_e6TwoThree_holds : GGTableBModuleInputOn GGE6TwoThreeLabel :=
  ggTableBModuleInputOn_of_irred ggBstarInnerDiagLInputOn_e6TwoThree
    ggTableBIrredInputOn_e6TwoThree

theorem ggTableBActionInputOn_e6TwoThree_holds : GGTableBActionInputOn GGE6TwoThreeLabel :=
  ggTableBActionInputOn_of_irred ggBstarInnerDiagLInputOn_e6TwoThree
    ggTableBIrredInputOn_e6TwoThree

theorem largeEvenLabelAll_noLine_e6TwoThree {p : ℕ} {lab : LargeEvenLabel}
    (h : GGE6TwoThreeLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineSCr p r R I := by
  have hp : p.Prime := h.2.2 ▸ Nat.prime_three
  exact (largeEvenLabelAll_torusIrred_e6TwoThree h).mono fun _ _ _ _ ⟨r, hl, hi⟩ =>
    ⟨r, hl, ggNoInvariantLineSCr_of_ggTorusIrred hp hi⟩

theorem ggLNoInvariantLineInputOn_e6TwoThree_holds : GGLNoInvariantLineInputOn GGE6TwoThreeLabel :=
  ggLNoInvariantLineInputOn_of_labelsSCr fun _ _ _ _ h => largeEvenLabelAll_noLine_e6TwoThree h

theorem ggTableBCxInputOn_of_not_e6TwoThree {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGE6TwoThreeLabel p lab) :
    GGTableBCxInputOn S :=
  (ggTableBCxInputOn_e6TwoThree_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGE6TwoThreeLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBModuleInputOn_of_not_e6TwoThree {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGE6TwoThreeLabel p lab) :
    GGTableBModuleInputOn S :=
  (ggTableBModuleInputOn_e6TwoThree_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGE6TwoThreeLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBActionInputOn_of_not_e6TwoThree {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGE6TwoThreeLabel p lab) :
    GGTableBActionInputOn S :=
  (ggTableBActionInputOn_e6TwoThree_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGE6TwoThreeLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggLNoInvariantLineInputOn_of_not_e6TwoThree {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLNoInvariantLineInputOn fun p lab => S p lab ∧ ¬ GGE6TwoThreeLabel p lab) :
    GGLNoInvariantLineInputOn S := by
  have h' := ggLNoInvariantLineInputOn_e6TwoThree_holds.or h
  intro G _ _ p B Bs x L D J hC hL E hEBs hxE hE
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_) E hEBs hxE hE
  by_cases h1 : GGE6TwoThreeLabel p lab
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

end Label

end CFSG.StandardType
