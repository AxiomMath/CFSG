module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolBase
public import CFSG.Quasithin.EmptyFaithful.SzF53BasC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Fn

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure ChartFacts (H M : Subgroup G) : Prop where
  inf_eq : ∀ β : Geo H M, vtype β = false → ∀ x ∈ stab β,
    (∀ l ∈ nbrs β, x ∈ Subgroup.normalizer (Zv l : Set G)) → x ∈ Qv β
  ex_out : ∀ β l : Geo H M, vtype β = false → l ∈ nbrs β →
    ∃ y ∈ stab β, y ∈ Subgroup.normalizer (Zv l : Set G) ∧ y ∉ stab l
  block : ∀ (β l : Geo H M) (P : Subgroup G), vtype β = false → l ∈ nbrs β →
    stab β ⊓ stab l ≤ P → P ≤ stab β →
      P ≤ Subgroup.normalizer (Zv l : Set G) ∨ P = stab β
  inter : ∀ (β l μ δ δ' : Geo H M), vtype β = false → l ∈ nbrs β → μ ∈ nbrs β → μ ≠ l →
    Zv μ = Zv l → l ∈ nbrs δ → δ ≠ β → μ ∈ nbrs δ' → δ' ≠ β →
      Vn β ⊓ Vn δ ⊓ (Vn β ⊓ Vn δ') ≤ Zv l

end S35.Fn

end F53.Stellmacher

end CFSG.Quasithin
