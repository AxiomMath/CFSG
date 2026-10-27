module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBIrred
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwE6Field
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTwE6TBLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1 ∧ 5 ≤ p

@[expose] def GGTwE6TorusIrredInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → 5 ≤ p →
    TwE6TB.GGTorusIrredSCr p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

@[expose] def GGTwE6NoTransvectionInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → 5 ≤ p →
    GGNoTransvectionSCr p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

section Certs34


namespace TwE6TB

theorem largeEvenLabelAll_pow_mem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twE6) (hpn : ¬ p ∣ lab.n) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I :=
  TwE6Delta.labelAll ht fun _ _ _ hK φ hφ =>
    TwE6Per.mem_recipeI_of_pow_eq_one hlab.1 hK hp hp2 hpn hφ

theorem ggBstarInnerDiagLInputOn_coprimeN :
    GGBstarInnerDiagLInputOn fun p lab => GGTwE6TBLabel p lab ∧ ¬ p ∣ lab.n :=
  CorFourTwoOpen.ggBstarInnerDiagLInputOn_of_pow ggLNoncyclicInput_holds
    fun _ _ hp hlab hs => largeEvenLabelAll_pow_mem hp
      (fun h2 => by have := hs.1.2.2; omega) hlab hs.1.1 hs.2

end TwE6TB

end Certs34

section Certs


namespace TwE6TB

theorem ggTorusLift_five {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hp : p.Prime) (hpn : p ∣ 2 ^ n + 1) (hp5 : 5 ≤ p) :
    GGTorusLift p 5 (TwE6Delta.RecipeR K n) := by
  have h := ggTorusLift_twE6Add_holds hn hK hp hpn
  rwa [TwE6Delta.liftRank_of_ne (by omega)] at h

end TwE6TB

theorem ggBstarInnerDiagLInputOn_twE6TB_of (hX : GGTwE6InnerDiagBound2LInput) :
    GGBstarInnerDiagLInputOn GGTwE6TBLabel := by
  have h := (ggBstarInnerDiagLInputOn_of_le_twE6Field hX
    (S := fun p lab => GGTwE6TBLabel p lab ∧ p ∣ lab.n)
    fun _ _ h => ⟨h.1.1, h.1.2.1, h.2⟩).or TwE6TB.ggBstarInnerDiagLInputOn_coprimeN
  have e : (fun p lab => (GGTwE6TBLabel p lab ∧ p ∣ lab.n) ∨
      (GGTwE6TBLabel p lab ∧ ¬ p ∣ lab.n)) = GGTwE6TBLabel := by
    funext p lab
    apply propext
    by_cases hpn : p ∣ lab.n <;> simp [hpn]
  rwa [e] at h

theorem largeEvenLabelAll_twE6TB_irred (hI : GGTwE6TorusIrredInput) {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGTwE6TBLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ TwE6TB.GGTorusIrredSCr p r R I :=
  TwE6Delta.labelAll h.1 fun K _ _ hK =>
    ⟨5, TwE6TB.ggTorusLift_five hlab.1 hK hp h.2.1 h.2.2,
      hI K lab.n p hlab.1 hK hp h.2.1 h.2.2⟩

theorem largeEvenLabelAll_twE6TB_line (hI : GGTwE6TorusIrredInput) {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGTwE6TBLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineSCr p r R I :=
  TwE6Delta.labelAll h.1 fun K _ _ hK =>
    ⟨5, TwE6TB.ggTorusLift_five hlab.1 hK hp h.2.1 h.2.2,
      TwE6TB.ggNoInvariantLineSCr_of_irredSCr hp (hI K lab.n p hlab.1 hK hp h.2.1 h.2.2)⟩

theorem largeEvenLabelAll_twE6TB_tv (hT : GGTwE6NoTransvectionInput) {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGTwE6TBLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoTransvectionSCr p r R I :=
  TwE6Delta.labelAll h.1 fun K _ _ hK =>
    ⟨5, TwE6TB.ggTorusLift_five hlab.1 hK hp h.2.1 h.2.2,
      hT K lab.n p hlab.1 hK hp h.2.1 h.2.2⟩

theorem ggTableBIrredInputOn_twE6TB_of (hI : GGTwE6TorusIrredInput) :
    GGTableBIrredInputOn GGTwE6TBLabel :=
  TwE6TB.ggTableBIrredInputOn_of_labelsSCr fun _ _ hp hlab hs =>
    largeEvenLabelAll_twE6TB_irred hI hp hlab hs

theorem ggTableBCxInputOn_twE6TB_of (hX : GGTwE6InnerDiagBound2LInput)
    (hI : GGTwE6TorusIrredInput) : GGTableBCxInputOn GGTwE6TBLabel :=
  ggTableBCxInputOn_of_irred (ggBstarInnerDiagLInputOn_twE6TB_of hX)
    (ggTableBIrredInputOn_twE6TB_of hI)

theorem ggTableBModuleInputOn_twE6TB_of (hX : GGTwE6InnerDiagBound2LInput)
    (hI : GGTwE6TorusIrredInput) : GGTableBModuleInputOn GGTwE6TBLabel :=
  ggTableBModuleInputOn_of_irred (ggBstarInnerDiagLInputOn_twE6TB_of hX)
    (ggTableBIrredInputOn_twE6TB_of hI)

theorem ggTableBActionInputOn_twE6TB_of (hX : GGTwE6InnerDiagBound2LInput)
    (hI : GGTwE6TorusIrredInput) : GGTableBActionInputOn GGTwE6TBLabel :=
  ggTableBActionInputOn_of_irred (ggBstarInnerDiagLInputOn_twE6TB_of hX)
    (ggTableBIrredInputOn_twE6TB_of hI)

theorem ggLNoInvariantLineInputOn_twE6TB_of (hI : GGTwE6TorusIrredInput) :
    GGLNoInvariantLineInputOn GGTwE6TBLabel :=
  ggLNoInvariantLineInputOn_of_labelsSCr fun _ _ hp hlab hs =>
    largeEvenLabelAll_twE6TB_line hI hp hlab hs

theorem ggLTransvectionCenterInputOn_twE6TB_of (hT : GGTwE6NoTransvectionInput) :
    GGLTransvectionCenterInputOn GGTwE6TBLabel :=
  TwE6TB.ggLTransvectionCenterInputOn_of_labelsSCr' ggLNoncyclicInput_holds fun _ _ hp hlab hs =>
    largeEvenLabelAll_twE6TB_tv hT hp hlab hs

theorem ggTableBCxInputOn_of_not_twE6TB (hX : GGTwE6InnerDiagBound2LInput)
    (hI : GGTwE6TorusIrredInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBCxInputOn fun p lab => S p lab ∧ ¬ GGTwE6TBLabel p lab) :
    GGTableBCxInputOn S := by
  have h' := (ggTableBCxInputOn_twE6TB_of hX hI).or h
  intro G _ _ p B Bs x L D J hcfg hM
  refine h' G p B Bs x L D J hcfg (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTwE6TBLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBModuleInputOn_of_not_twE6TB (hX : GGTwE6InnerDiagBound2LInput)
    (hI : GGTwE6TorusIrredInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBModuleInputOn fun p lab => S p lab ∧ ¬ GGTwE6TBLabel p lab) :
    GGTableBModuleInputOn S := by
  have h' := (ggTableBModuleInputOn_twE6TB_of hX hI).or h
  intro G _ _ p B Bs x L D J hcfg hM
  refine h' G p B Bs x L D J hcfg (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTwE6TBLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBActionInputOn_of_not_twE6TB (hX : GGTwE6InnerDiagBound2LInput)
    (hI : GGTwE6TorusIrredInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGTwE6TBLabel p lab) :
    GGTableBActionInputOn S := by
  have h' := (ggTableBActionInputOn_twE6TB_of hX hI).or h
  intro G _ _ p B Bs x L D J B₂ hcfg hM
  refine h' G p B Bs x L D J B₂ hcfg (hM.mono fun p lab hlab => ?_)
  by_cases hl : GGTwE6TBLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

theorem ggLNoInvariantLineInputOn_of_not_twE6TB (hI : GGTwE6TorusIrredInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLNoInvariantLineInputOn fun p lab => S p lab ∧ ¬ GGTwE6TBLabel p lab) :
    GGLNoInvariantLineInputOn S := by
  have h' := (ggLNoInvariantLineInputOn_twE6TB_of hI).or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases hl : GGTwE6TBLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

theorem ggLTransvectionCenterInputOn_of_not_twE6TB (hT : GGTwE6NoTransvectionInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab => S p lab ∧ ¬ GGTwE6TBLabel p lab) :
    GGLTransvectionCenterInputOn S := by
  have h' := (ggLTransvectionCenterInputOn_twE6TB_of hT).or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases hl : GGTwE6TBLabel p lab
  · exact Or.inl hl
  · exact Or.inr ⟨hlab, hl⟩

end Certs

end CFSG.StandardType

end
