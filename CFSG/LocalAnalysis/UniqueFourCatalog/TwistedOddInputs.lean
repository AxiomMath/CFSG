module

public import CFSG.Yardstones.Mf4cdcdf2e013.Definitions

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

@[expose] def TwistedE6OddExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → ∀ p f : ℕ, p ≠ 2 →
    ChevalleyExceptionalModel G .twistedE6 p f → False

@[expose] def TrialityD4OddExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → ∀ p f : ℕ, p ≠ 2 →
    ChevalleyExceptionalModel G .trialityD4 p f → False

@[expose] def UntwistedExceptionalOddExclusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Standing4 G → ∀ (t : StatedLieTag),
    (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) → ∀ p f : ℕ, p ≠ 2 →
      ChevalleyExceptionalModel G t p f → False

end CFSG.LocalAnalysis.UniqueFourCatalog
