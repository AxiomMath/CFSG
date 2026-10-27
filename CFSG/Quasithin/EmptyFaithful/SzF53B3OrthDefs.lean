module

public import CFSG.Quasithin.EmptyFaithful.SzF53B3Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53 CFSG.Quasithin.F53Mod
open CFSG.Quasithin.CosetGeom

namespace F53B3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure OrthC1 (H M S : Subgroup G) : Prop where
  cv_eq : ∀ β : Geo H M, vtype β = false → Cv β = Zv β
  card_R : ∀ x y μ : Geo H M, x ≠ y → vtype μ = true → (graph (H ⊔ M) H M).Adj μ x →
    (graph (H ⊔ M) H M).Adj μ y → Nat.card ↥(Vn x ⊓ Vn y) = 8
  zv_le_comm : ∀ x y μ : Geo H M, x ≠ y → vtype μ = true → (graph (H ⊔ M) H M).Adj μ x →
    (graph (H ⊔ M) H M).Adj μ y → Zv μ ≤ ⁅Vn x ⊓ Vn y, Qv μ⁆

structure OrthS4 (H M S : Subgroup G) : Prop where
  index_two : ∀ x y μ : Geo H M, x ≠ y → vtype μ = true → (graph (H ⊔ M) H M).Adj μ x →
    (graph (H ⊔ M) H M).Adj μ y → (Vn x ⊓ Qv y).relIndex (Vn x) = 2
  le_A5 : ∀ x y μ : Geo H M, x ≠ y → vtype μ = true → (graph (H ⊔ M) H M).Adj μ x →
    (graph (H ⊔ M) H M).Adj μ y → Vn x ≤ oTwoRes (stab y) ⊔ Qv y

end F53B3

end CFSG.Quasithin
