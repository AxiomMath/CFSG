module

public import CFSG.Quasithin.EmptyFaithful.S153D29

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

structure Ctx15330 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) :
    Prop extends Ctx15328 T Mc M V₁ V₂ Yp I L t where
  c28 : Concl15328 T M V₁ I L
  c29 : Concl15329 T M V₁ Yp I

@[expose] def Input15330 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15330 T Mc M V₁ V₂ Yp I L t → ¬ ∃ n : ℕ, 1 < n ∧ IsPSL 2 2 n ↥(Star153 T I L)

end CFSG.Quasithin
