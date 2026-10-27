module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGNbrTableBWeylInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenHalfSplit p lab True → GGNbrSplitLabel p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusReflGenW p r R I

theorem GGNbrTableBWeylInputOn.of_cover {S T U : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGNbrTableBWeylInputOn S) (h₂ : GGNbrTableBWeylInputOn T)
    (h : ∀ p lab, U p lab → S p lab ∨ T p lab) : GGNbrTableBWeylInputOn U := by
  intro p hp hp2 lab hlab hU hhs hsp
  rcases h p lab hU with hS | hT
  · exact h₁ p hp hp2 lab hlab hS hhs hsp
  · exact h₂ p hp hp2 lab hlab hT hhs hsp

theorem ggNbrTableBWeylInput_of_on {S : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGNbrTableBWeylInputOn S) (h₂ : GGNbrTableBWeylInputOn fun p lab => ¬ S p lab) :
    GGNbrTableBWeylInput := by
  intro p hp hp2 lab hlab hhs hsp
  by_cases hS : S p lab
  · exact h₁ p hp hp2 lab hlab hS hhs hsp
  · exact h₂ p hp hp2 lab hlab hS hhs hsp

end CFSG.StandardType
