module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.F7Geometry
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.EmptyFaithful.S152XA5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X

structure F53Amalgam {G : Type} [Group G] [Finite G] (H M S : Subgroup G) : Prop where
  amalgam : AmalgamHyp (H ⊔ M) H M S
  inf_eq : H ⊓ M = S
  charTwo_right : CharTwo M
  quot_left : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 5))
  quot_right : Nonempty (OTwoQuot M ≃* Equiv.Perm (Fin 3))
  quasithin : IsQuasithinSub (H ⊔ M)

structure F53EData {G : Type} [Group G] (H S E : Subgroup G) : Prop where
  le : E ≤ S
  abelian : IsElemAbelian 2 E
  normal : H ≤ Subgroup.normalizer (E : Set G)
  chief : IsChiefSeriesFrom H E E 2
  shape : ∀ L N : Subgroup G, IsChiefStep H E L N → ¬ IsCentralStep H L N →
    ChiefFactorShape H L N

@[expose] def F53AmalgamStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S →
    ∀ E : Subgroup G, F53EData H S E → Nat.card E < 64

end CFSG.Quasithin
