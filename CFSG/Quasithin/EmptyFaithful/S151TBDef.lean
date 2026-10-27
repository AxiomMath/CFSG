module

public import CFSG.Quasithin.EmptyFaithful.S151XF

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G]

abbrev LStar (L : Subgroup G) : Type := ↥L ⧸ CFSG.pCore 2 ↥L

@[expose] def ListD' (L : Subgroup G) : Prop :=
  IsAlt 7 (LStar L ⧸ Subgroup.center (LStar L)) ∨ IsAlt 6 (LStar L ⧸ Subgroup.center (LStar L)) ∨
    IsPSU 3 3 1 (LStar L ⧸ Subgroup.center (LStar L))

theorem listD_iff_or {L : Subgroup G} :
    ListD15120 L ↔ ListD' L ∨ IsPSL 3 2 1 (LStar L ⧸ Subgroup.center (LStar L)) := by
  unfold ListD15120 ListD'
  constructor
  · rintro (h | h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
  · rintro ((h | h | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)

end CFSG.Quasithin.S151TB
