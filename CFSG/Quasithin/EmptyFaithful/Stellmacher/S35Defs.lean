module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53.Stellmacher

open CosetGeom F53

namespace S35

variable {G : Type} [Group G] [Finite G]

@[expose] def CaseII (H M : Subgroup G) : Prop :=
  ∀ β l δ : Geo H M, vtype β = false → l ∈ nbrs β → l ∈ nbrs δ → δ ≠ β →
    Vn β ⊓ Vn δ = Zv l

end S35

end F53.Stellmacher

end CFSG.Quasithin
