module

public import CFSG.Adapters.Involutions

public section

universe u v w

namespace CFSG.BrauerSuzuki

open CFSG CFSG in
theorem _root_.CFSG.Milestones.brauer_suzuki {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 3 ≤ n)
    (P : Sylow 2 G)
    (hquat : Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2))))
    (t : G) (ht_mem : t ∈ (P : Subgroup G)) (ht_ord : orderOf t = 2) :
    (QuotientGroup.mk t : G ⧸ oddCore G) ∈
      Subgroup.center (G ⧸ oddCore G) :=
  _root_.CFSG.BrauerSuzuki.brauer_suzuki n hn P hquat t ht_mem ht_ord

end CFSG.BrauerSuzuki

namespace CFSG.Adapters

open CFSG in
theorem _root_.CFSG.Milestones.brauer_suzuki_central_involution {G : Type*} [Group G] [Finite G]
    (n : ℕ) (hn : 3 ≤ n)
    (P : Sylow 2 G)
    (hquat : Nonempty ((P : Subgroup G) ≃* QuaternionGroup (2 ^ (n - 2))))
    (t : G) (ht_mem : t ∈ (P : Subgroup G)) (ht_ord : orderOf t = 2) :
    (QuotientGroup.mk t : G ⧸ oddCore G) ≠ 1 ∧
      (QuotientGroup.mk t : G ⧸ oddCore G) ∈ Subgroup.center (G ⧸ oddCore G) :=
  _root_.CFSG.Adapters.brauer_suzuki n hn P hquat t ht_mem ht_ord

end CFSG.Adapters
