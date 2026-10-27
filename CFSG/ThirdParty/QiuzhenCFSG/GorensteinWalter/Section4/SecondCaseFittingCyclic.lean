module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingCyclicCardLe

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the cyclic fixed-part transfer

This compatibility wrapper exposes the cyclicity part of the stronger
equation-(6) transfer, which also controls the cardinality of the fixed part.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A conjugate disjoint from a normal fixed part embeds in the cyclic
quotient supplied by the inverted part. -/
public theorem secondCase_fitting_fixed_part_cyclic_of_conjugate_disjoint
    {G : Type u} [Group G] [Finite G]
    (K0 F Y : Subgroup G)
    (hK0cyc : IsCyclic K0)
    (hFnormal : IsNormalIn F Y)
    (hjoin : K0 ⊔ F = Y)
    (g : G)
    (hYnormg : g ∈ Subgroup.normalizer (Y : Set G))
    (hdisj : F ⊓ conjugateSubgroup F g = ⊥) :
    IsCyclic F :=
  (secondCase_fitting_fixed_part_cyclic_and_card_le_of_conjugate_disjoint
    K0 F Y hK0cyc hFnormal hjoin g hYnormg hdisj).1

end CFSG.GorensteinWalter
