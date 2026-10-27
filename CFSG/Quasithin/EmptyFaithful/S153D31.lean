module

public import CFSG.Quasithin.EmptyFaithful.S153D30

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

structure Ctx15331 {G : Type} [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G) :
    Prop extends Ctx15330 T Mc M V₁ V₂ Yp I L t where
  c30 : ¬ ∃ n : ℕ, 1 < n ∧ IsPSL 2 2 n ↥(Star153 T I L)

@[expose] def Input15331 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    Ctx15331 T Mc M V₁ V₂ Yp I L t → Nonempty (↥(Star153 T I I) ≃* Equiv.Perm (Fin 8))

end CFSG.Quasithin
