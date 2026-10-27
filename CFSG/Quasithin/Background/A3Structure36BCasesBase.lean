
module

public import CFSG.Quasithin.Background.A3StructureDefs

@[expose] public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement
open CFSG.SectionRank CFSG.SectionRank.Ccomm

variable {X : Type} [Group X]

theorem isSL2_quotient_congr {r : ℕ} {A B : Subgroup X} [A.Normal] [B.Normal] (hAB : A = B)
    (h : IsSL2 r (X ⧸ A)) : IsSL2 r (X ⧸ B) := by
  obtain ⟨e⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hAB).symm.trans e⟩

end CFSG.Quasithin.A36B
