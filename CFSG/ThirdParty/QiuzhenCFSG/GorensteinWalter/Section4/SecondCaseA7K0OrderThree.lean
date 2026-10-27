module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7K0QuotientCard
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: an order-three element in the inverted fitting part
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A quotient image of cardinality three forces an ambient order-three
element in the corresponding subgroup. -/
public theorem secondCase_a7_k0_exists_order_three
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} (O : Subgroup M) [O.Normal]
    (K0 : Subgroup G) (hK0leM : K0 ≤ M)
    (hcard : Nat.card ((K0.subgroupOf M).map
      (QuotientGroup.mk' O)) = 3) :
    ∃ x : G, x ∈ K0 ∧ orderOf x = 3 := by
  let q : M →* M ⧸ O := QuotientGroup.mk' O
  have hdiv : 3 ∣ Nat.card (K0.subgroupOf M) := by
    have hmap := Subgroup.card_map_dvd (K0.subgroupOf M) q
    rw [hcard] at hmap
    exact hmap
  obtain ⟨x, hxorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := K0.subgroupOf M) 3 hdiv
  refine ⟨(x : G), ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.mp x.property
  · have hxM : orderOf (x : G) = orderOf x := by
      have h1 : orderOf (x : G) = orderOf (x : M) :=
        orderOf_injective M.subtype M.subtype_injective (x : M)
      have h2 : orderOf (x : M) = orderOf x :=
        orderOf_injective (K0.subgroupOf M).subtype
          (K0.subgroupOf M).subtype_injective x
      exact h1.trans h2
    rw [hxM]
    exact hxorder

end CFSG.GorensteinWalter
