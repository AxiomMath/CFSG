module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListCorrected
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenTriDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open

@[expose] def OddTranspositionListInputClsTri : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X →
    OddTranspListAlt X s ∨ IsTrialityOddTransp (X ⧸ Subgroup.center X) (QuotientGroup.mk s)

@[expose] def OddTranspListExtTriality : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    CFSG.Timmesfeld.Bridge.Asc72.IsOddTransp {x : X | IsConj s x} →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → CFSG.pCore 2 X = ⊥ →
    fusionOddCore X ≤ Subgroup.center X → OddTranspListExt X s →
    OddTranspListAlt X s ∨ IsTrialityOddTransp (X ⧸ Subgroup.center X) (QuotientGroup.mk s)

@[expose] def TrialityCentralInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : X), orderOf s = 2 →
    Subgroup.normalClosure ({s} : Set X) = ⊤ → Odd (Nat.card (Subgroup.center X)) →
    IsTrialityOddTransp (X ⧸ Subgroup.center X) (QuotientGroup.mk s) →
    Subgroup.center X = ⊥

theorem oddTranspositionListInputClsTri_of_ext (hC : OddTranspositionListInputClsCorrected)
    (hE : OddTranspListExtTriality) : OddTranspositionListInputClsTri := by
  intro X _ _ s hord hodd hncl hpc hOZ
  rcases hC X s hord hodd hncl hpc hOZ with h | h
  · exact Or.inl h
  · exact hE X s hord hodd hncl hpc hOZ h

end CFSG.LocalAnalysis.WeakClosure81
