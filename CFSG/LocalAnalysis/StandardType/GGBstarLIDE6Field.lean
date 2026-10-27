module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExc

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGE6ThreeFieldLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1 ∧ 3 ∣ lab.n

@[expose] def GGE6InnerDiagBoundThreeInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = 2 ^ n → 3 ∣ 2 ^ n - 1 →
    3 ∣ n → GGInnerDiagBound 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)

section Certs


theorem largeEvenLabelAll_e6ThreeField_bound (hX : GGE6InnerDiagBoundThreeInput) {p : ℕ}
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGE6ThreeFieldLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, rfl, h3, h3n⟩ := h
  have hn : 1 ≤ n := hlab.1
  dsimp only at htag h3 h3n hn
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  have h1 := TableBExc.recipeChevalleyE6_torusLift_three h3 hQ
  obtain ⟨K, _, _, hK, hQK, hl⟩ := h1
  exact ⟨K, inferInstance, inferInstance, hK, hQK, 5, hl, hX K n hn hK h3 h3n⟩

theorem ggBstarInnerDiagLInputOn_of_le_e6ThreeField
    (hX : GGE6InnerDiagBoundThreeInput) {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGE6ThreeFieldLabel p lab) : GGBstarInnerDiagLInputOn S :=
  ggBstarInnerDiagLInputOn_of_labels' ggLNoncyclicInput_holds fun _ _ _ hlab hs =>
    largeEvenLabelAll_e6ThreeField_bound hX hlab (hS _ _ hs)

theorem ggBstarInnerDiagLInputOn_of_not_e6ThreeField
    (hX : GGE6InnerDiagBoundThreeInput) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGBstarInnerDiagLInputOn fun p lab => S p lab ∧ ¬ GGE6ThreeFieldLabel p lab) :
    GGBstarInnerDiagLInputOn S := by
  have hF := ggBstarInnerDiagLInputOn_of_le_e6ThreeField hX
    (S := fun p lab => S p lab ∧ GGE6ThreeFieldLabel p lab) fun _ _ h => h.2
  have h' := hF.or h
  intro G _ _ p B Bs x L D J hC hL
  refine (h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)).mono fun p lab hlab => ?_
  · by_cases hl : GGE6ThreeFieldLabel p lab
    · exact Or.inl ⟨hlab, hl⟩
    · exact Or.inr ⟨hlab, hl⟩
  · rcases hlab with h1 | h1
    · exact h1.1
    · exact h1.1

end Certs

end CFSG.StandardType
