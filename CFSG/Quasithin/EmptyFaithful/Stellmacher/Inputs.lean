module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasC
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

@[expose] def Hss15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X V : Subgroup G),
    Nonempty (OTwoQuot X ≃* Equiv.Perm (Fin 5)) → V ≤ pCoreOf 2 X →
    X ≤ Subgroup.normalizer (V : Set G) → IsElemAbelian 2 V →
    X ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 X →
    ∀ s ∈ X, (V ⊓ Subgroup.centralizer ({s} : Set G)).relIndex V = 2 →
    IsOrthSec X (V ⊓ Subgroup.centralizer (X : Set G)) V

variable {G : Type} [Group G] [Finite G]

@[expose] def Hss27At (H M : Subgroup G) : Prop :=
  2 ≤ bMin H M → ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → bAt α = bMin H M →
    stab α ≤ Subgroup.normalizer ((Zv α ⊔ Zv β : Subgroup G) : Set G) →
    Zv β ≤ centerOf (stab β)

@[expose] def Hss27S5At (H M : Subgroup G) : Prop :=
  2 ≤ bMin H M → ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → vtype α = false →
    bAt α = bMin H M → stab α ≤ Subgroup.normalizer ((Zv α ⊔ Zv β : Subgroup G) : Set G) →
    Zv β ≤ centerOf (stab β)

end F53.Stellmacher

end CFSG.Quasithin
