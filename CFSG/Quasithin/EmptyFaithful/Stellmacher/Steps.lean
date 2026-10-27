module

public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs
public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom

section At

variable {G : Type} [Group G] [Finite G]

@[expose] def Hss28At (H M : Subgroup G) : Prop :=
  1 < bMin H M → ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → bAt α = bMin H M →
    Qv α ⊔ Qv β = stab α ⊓ stab β

@[expose] def Hss32At (H M : Subgroup G) : Prop :=
  ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → vtype α = true → bAt α = bMin H M →
    Zv β ≤ centerOf (stab β)

@[expose] def Hss33At (H M : Subgroup G) : Prop :=
  ∀ α β α' : Geo H M, IsCritData α β α' → vtype α = true → ⁅Zv α, Zv α'⁆ ≠ ⊥ → bMin H M = 2

@[expose] def Hss34At (H M : Subgroup G) : Prop :=
  ∀ α β α' : Geo H M, IsCritData α β α' → vtype α = true → ⁅Zv α, Zv α'⁆ = ⊥ →
    Nat.card (Zv α) = 4 ∧ Nat.card (Zv β) = 2 ∧ 1 < bMin H M ∧
      (IsNatSec (stab β) (Vn β ⊓ Subgroup.centralizer (oTwoRes (stab β) : Set G)) (Vn β) ∨
        IsOrthSec (stab β) (Vn β ⊓ Subgroup.centralizer (oTwoRes (stab β) : Set G)) (Vn β))

@[expose] def Hss36At (H M : Subgroup G) : Prop :=
  ∀ α β α' : Geo H M, IsCritData α β α' → vtype α = true → ⁅Zv α, Zv α'⁆ = ⊥ → bMin H M = 3

@[expose] def Hss41At (H M : Subgroup G) : Prop :=
  ∀ α β : Geo H M, (graph (H ⊔ M) H M).Adj α β → vtype α = false → bAt α = bMin H M →
    bMin H M < bAt β → Zv β ≤ centerOf (stab β)

@[expose] def Hss42At (H M : Subgroup G) : Prop :=
  ∀ α : Geo H M, vtype α = false → bAt α = bMin H M →
    (∀ β : Geo H M, (graph (H ⊔ M) H M).Adj α β → bMin H M < bAt β) →
    IsOrthSec (stab α) ⊥ (Zv α) ∨ IsNatSec (stab α) ⊥ (Zv α)

@[expose] def Hss43At (H M : Subgroup G) : Prop :=
  ∀ α : Geo H M, vtype α = false → bAt α = bMin H M →
    (∀ β : Geo H M, (graph (H ⊔ M) H M).Adj α β → bMin H M < bAt β) →
    IsOrthSec (stab α) ⊥ (Zv α) → bMin H M = 1

end At

@[expose] def Hss33 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S → Hss33At H M

@[expose] def Hss34 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S → Hss34At H M

@[expose] def Hss43 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M S : Subgroup G), F53Amalgam H M S → Hss43At H M

end F53.Stellmacher

end CFSG.Quasithin
