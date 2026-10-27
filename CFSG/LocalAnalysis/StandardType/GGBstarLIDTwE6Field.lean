module

public import CFSG.LocalAnalysis.StandardType.GGBstarLemmaC
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTwE6FieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1 ∧ p ∣ lab.n

@[expose] def GGTwE6InnerDiagBound2LInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    p ∣ 2 ^ n + 1 → p ∣ n →
    GGInnerDiagBound2L p (TwE6Delta.liftRank p) (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

section Certs


theorem largeEvenLabelAll_twE6Field_bound2L (hX : GGTwE6InnerDiagBound2LInput) {p : ℕ}
    (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGTwE6FieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound2L p r R I ∧ GGOutdiagOdd p R I :=
  TwE6Delta.labelAll h.1 fun K _ _ hK =>
    ⟨_, ggTorusLift_twE6Add_holds hlab.1 hK hp h.2.1, hX K lab.n p hlab.1 hK hp h.2.1 h.2.2,
      TwE6Delta.ggOutdiagOdd_twE6 hlab.1 hK p⟩

theorem ggBstarInnerDiagLInputOn_of_le_twE6Field (hX : GGTwE6InnerDiagBound2LInput)
    {S : ℕ → LargeEvenLabel → Prop} (hS : ∀ p lab, S p lab → GGTwE6FieldLabel p lab) :
    GGBstarInnerDiagLInputOn S :=
  ggBstarInnerDiagLInputOn_of_labels2L ggLNoncyclicInput_holds fun _ _ hp hlab hs =>
    largeEvenLabelAll_twE6Field_bound2L hX hp hlab (hS _ _ hs)

theorem ggBstarInnerDiagLInputOn_of_not_twE6Field (hX : GGTwE6InnerDiagBound2LInput)
    {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarInnerDiagLInputOn fun p lab => S p lab ∧ ¬ GGTwE6FieldLabel p lab) :
    GGBstarInnerDiagLInputOn S := by
  have hF := ggBstarInnerDiagLInputOn_of_le_twE6Field hX
    (S := fun p lab => S p lab ∧ GGTwE6FieldLabel p lab) fun _ _ h => h.2
  have h' := hF.or h
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)).mono fun p lab hlab => ?_
  · by_cases hl : GGTwE6FieldLabel p lab
    · exact Or.inl ⟨hlab, hl⟩
    · exact Or.inr ⟨hlab, hl⟩
  · rcases hlab with h1 | h1
    · exact h1.1
    · exact h1.1

end Certs

end CFSG.StandardType
