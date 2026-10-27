module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs
public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53

variable {G : Type} [Group G] [Finite G]

open CosetGeom

structure F53DichAt2 (H M : Subgroup G) : Prop where
  s3_range : ∀ α : Geo H M, bAt α = bMin H M → vtype α = true →
    2 ≤ bMin H M ∧ bMin H M ≤ 3
  zv_central : ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → bAt α = bMin H M →
    Zv β ≤ centerOf (stab β)
  s5_module : ∀ α : Geo H M, bAt α = bMin H M → vtype α = false →
    (IsOrthSec (stab α) ⊥ (Zv α) ∨ IsNatSec (stab α) ⊥ (Zv α)) ∧
    (1 < bMin H M → IsNatSec (stab α) ⊥ (Zv α))
  s3_three : ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → bAt α = bMin H M →
    vtype α = true → bMin H M = 3 →
    Qv α ⊔ Qv β = stab α ⊓ stab β ∧ Nat.card (Zv β) = 2 ∧
    (IsNatSec (stab β) (Vn β ⊓ Subgroup.centralizer (oTwoRes (stab β) : Set G)) (Vn β) ∨
      IsOrthSec (stab β) (Vn β ⊓ Subgroup.centralizer (oTwoRes (stab β) : Set G)) (Vn β))

end F53

@[expose] def F53Dichotomy2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S → F53.F53DichAt2 H M

end CFSG.Quasithin
