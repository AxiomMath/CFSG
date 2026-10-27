module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasC
public import CFSG.Quasithin.EmptyFaithful.SzF53MDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher.S43

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure Sit43 (α : Geo H M) : Prop where
  vα : vtype α = false
  bα : bAt α = bMin H M
  lt : ∀ β : Geo H M, (graph (H ⊔ M) H M).Adj α β → bMin H M < bAt β
  orth : IsOrthSec (stab α) ⊥ (Zv α)
  b1 : 1 < bMin H M

@[expose] def Yv (δ : Geo H M) : Subgroup G := ⨅ (l : Geo H M) (_ : l ∈ nbrs δ), Zv l

@[expose] def Qst (δ : Geo H M) : Subgroup G := Qv δ ⊓ Subgroup.centralizer (Yv δ : Set G)

@[expose] def Cst (δ : Geo H M) : Subgroup G := Qv δ ⊓ Subgroup.centralizer (Vn δ : Set G)

@[expose] def Vst (δ : Geo H M) : Subgroup G := ⁅Vn δ, Qv δ⁆

@[expose] def Lres (δ : Geo H M) : Subgroup G := oTwoRes (stab δ)

@[expose] def Wn (δ : Geo H M) : Subgroup G := ⨆ (l : Geo H M) (_ : dist l δ = 2), Zv l

end F53.Stellmacher.S43

end CFSG.Quasithin
