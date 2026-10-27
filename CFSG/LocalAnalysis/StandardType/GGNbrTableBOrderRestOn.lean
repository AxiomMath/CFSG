module

public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKnownDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGNbrTableBOrderRestInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (lab : LargeEvenLabel) (N : ℕ), LargeEvenInLambda2 lab →
    S p lab → GGNbrSplitLabel p lab → GGTableBOrderRest lab N →
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusAutCardDvdSCr p r R I N

theorem GGNbrTableBOrderRestInputOn.of_cover {S T U : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGNbrTableBOrderRestInputOn S) (h₂ : GGNbrTableBOrderRestInputOn T)
    (h : ∀ p lab, U p lab → S p lab ∨ T p lab) : GGNbrTableBOrderRestInputOn U := by
  intro p hp hp2 lab N hlab hU hsp hN
  rcases h p lab hU with hS | hT
  · exact h₁ p hp hp2 lab N hlab hS hsp hN
  · exact h₂ p hp hp2 lab N hlab hT hsp hN

theorem ggNbrTableBOrderRestInput_of_on {S : ℕ → LargeEvenLabel → Prop}
    (h₁ : GGNbrTableBOrderRestInputOn S)
    (h₂ : GGNbrTableBOrderRestInputOn fun p lab => ¬ S p lab) : GGNbrTableBOrderRestInput := by
  intro p hp hp2 lab N hlab hsp hN
  by_cases hS : S p lab
  · exact h₁ p hp hp2 lab N hlab hS hsp hN
  · exact h₂ p hp hp2 lab N hlab hS hsp hN

end CFSG.StandardType
