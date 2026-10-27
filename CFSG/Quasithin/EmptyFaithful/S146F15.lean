module

public import CFSG.Quasithin.EmptyFaithful.S146F14
public import CFSG.Quasithin.EmptyFaithful.S146F7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

section Defs

variable {G : Type} [Group G]

@[expose] def Ctx15 (T M H : Subgroup G) (p : ℕ) (H₁ : Subgroup G) : Prop :=
  p = 5 ∧ Case13Two T M H p H₁ ∧ (Stage14614C1 T H p ∨ Stage14614C4 T H p)

end Defs

end CFSG.Quasithin
