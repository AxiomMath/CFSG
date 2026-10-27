module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerConjugate
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FittingSubgroupConjugate

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugation transport for generalized Fitting subgroups

This combines the Fitting-subgroup and component-layer transport theorems.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

/-- Conjugating a subgroup conjugates its generalized Fitting subgroup. -/
public theorem generalizedFittingSubgroupOf_conjugateSubgroup
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (g : G) :
    generalizedFittingSubgroupOf (conjugateSubgroup A g) =
      (generalizedFittingSubgroupOf A).map (MulAut.conj g).toMonoidHom := by
  rw [generalizedFittingSubgroupOf, generalizedFittingSubgroupOf,
    fittingSubgroupOf_conjugateSubgroup, componentLayerOf_conjugateSubgroup,
    Subgroup.map_sup]

end

end CFSG.GorensteinWalter
