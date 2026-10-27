module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Kb (β : Geo H M) : Subgroup G := Qv β ⊓ Subgroup.centralizer (Vn β : Set G)

@[expose] def Lr (δ : Geo H M) : Subgroup G := oTwoRes (stab δ)

@[expose] def Wb (β : Geo H M) : Subgroup G := ⨆ (ρ : Geo H M) (_ : dist ρ β = 2), Vn ρ

@[expose] def Wl (l : Geo H M) : Subgroup G := ⨆ (ρ : Geo H M) (_ : ρ ∈ nbrs l), Vn ρ

@[expose] def CaseI (H M : Subgroup G) : Prop :=
  ∀ β l δ : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → δ ≠ β →
    Nat.card ↥(Vn β ⊓ Vn δ) = 8 ∧ Nat.card ↥(Vn β) = 32

@[expose] def Lam (δ δ' : Geo H M) : Prop := S34.PD δ δ' ∧ ¬ Zv δ ≤ Vn δ'

@[expose] def Delta0 (β α' : Geo H M) : Set (Geo H M) :=
  {l | l ∈ nbrs β ∧ ¬ Vn α' ≤ Subgroup.normalizer (Zv l : Set G)}

end S35

end F53.Stellmacher

end CFSG.Quasithin
