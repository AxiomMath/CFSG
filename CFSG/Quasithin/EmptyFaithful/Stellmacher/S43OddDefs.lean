module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Statements
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

variable {G : Type} [Group G] [Finite G]

@[expose] def IsCritPair₃ {H M : Subgroup G} (δ δ' : Geo H M) : Prop :=
  vtype δ = true ∧ vtype δ' = true ∧ dist δ δ' + 1 = bMin H M ∧ ¬ Vn δ ≤ Qv δ'

@[expose] def AtMostOneNoncentral {H M : Subgroup G} (α : Geo H M) : Prop :=
  ∃ (r : ℕ) (W : ℕ → Subgroup G), W 0 = Zv α ∧ W r = Wn α ∧
    (∀ i, i < r → IsChiefStep (stab α) (pCoreOf 2 (stab α)) (W i) (W (i + 1))) ∧
    ∀ i j, i < r → j < r → i ≠ j →
      IsCentralStep (stab α) (W i) (W (i + 1)) ∨ IsCentralStep (stab α) (W j) (W (j + 1))

@[expose] def Gap7At (H M : Subgroup G) : Prop :=
  ∀ S : Subgroup G, F53Amalgam H M S → Hss26AAt H M → ∀ α : Geo H M, Sit43 α →
    bMin H M = 3 → ∀ β : Geo H M, β ∈ nbrs α → Nat.card (Vn β) = 2 ^ 6 → False

@[expose] def OddEndAt (H M : Subgroup G) : Prop :=
  ∀ S : Subgroup G, F53Amalgam H M S → Hss26AAt H M → ∀ α : Geo H M, Sit43 α →
    Odd (bMin H M) → 7 ≤ bMin H M → ∀ β : Geo H M, β ∈ nbrs α → Nat.card (Vn β) = 2 ^ 6 → False

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
