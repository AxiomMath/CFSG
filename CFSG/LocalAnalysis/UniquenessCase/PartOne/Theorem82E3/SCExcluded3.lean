module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Context

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

@[expose] def Ctx82E3.IsSCPrime (c : Ctx82E3 D) (p : ℕ) : Prop :=
  p ∈ D.sig ∧ ¬ p ∣ ((c.L).subgroupOf D.M).index

@[expose] def Ctx82E3.SCExcluded3 (c : Ctx82E3 D) : Prop :=
  ∀ p : ℕ, c.IsSCPrime p → False

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
