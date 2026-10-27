module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer

namespace CFSG
end CFSG
open CFSG

/-!
# Controlling order-three normalizers
-/

namespace CFSG.GorensteinWalter

universe u

/-- If a subgroup contains the centralizer of an order-three subgroup and
also contains a square-one element that normalizes and inverts it, then it
contains the full normalizer. -/
public theorem normalizer_le_of_centralizer_le_of_card_eq_three
    {G : Type u} [Group G] [Finite G]
    (X N : Subgroup G) (hXcard : Nat.card X = 3)
    {u : G} (huSq : u ^ 2 = 1)
    (huNorm : u ∈ Subgroup.normalizer (X : Set G))
    (huInv : ∀ x : G, x ∈ X → u * x * u⁻¹ = x⁻¹)
    (hCentLe : Subgroup.centralizer (X : Set G) ≤ N)
    (huN : u ∈ N) :
    Subgroup.normalizer (X : Set G) ≤ N := by
  rw [normalizer_eq_centralizer_sup_zpowers_of_card_eq_three
    X hXcard huSq huNorm huInv]
  exact sup_le hCentLe (Subgroup.zpowers_le.mpr huN)

end CFSG.GorensteinWalter
