module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerConjugate
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentCentralizingFittingLeLayer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentLayerCentralizesSolvableNormalized

namespace CFSG
end CFSG
open CFSG

/-!
# Component-layer containment for Gorenstein--Walter Lemma 2.5

The control core puts `E(A)` inside the conjugate maximal subgroup `B`.
The Fitting subgroup of `B` is solvable and normal in `B`, so `E(A)`
centralizes it.  The `D`-group component-absorption theorem then gives
`E(A) ≤ E(B)`.  Conjugation preserves the cardinality of the layer, hence
the inclusion is equality and `E(B) ≤ A`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the non-`p` branch of Lemma 2.5, Fitting containment for the
controlled conjugate forces the corresponding component-layer containment. -/
public theorem componentLayerOf_conjugateSubgroup_le_of_minimalCounterexample_of_controlCore_of_fitting_le
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (A : Subgroup G) (hA : IsCoatom A) (g : G)
    (hC : ControlCore A (conjugateSubgroup A g))
    (hFB : fittingSubgroupOf (conjugateSubgroup A g) ≤ A) :
    componentLayerOf (conjugateSubgroup A g) ≤ A := by
  classical
  let B : Subgroup G := conjugateSubgroup A g
  change componentLayerOf B ≤ A
  change ControlCore A B at hC
  change fittingSubgroupOf B ≤ A at hFB
  have hB : IsCoatom B := by
    dsimp [B, conjugateSubgroup]
    exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup A).2 hA
  have hD : IsDGroup B :=
    properSubgroups_areDGroups hmin B hB.ne_top
  rcases hC with ⟨S, _hSne, hSF, hSB, hSsub, hCS⟩
  have hEAleB : componentLayerOf A ≤ B :=
    (fstar_componentLayer_le_selfCentralizingSubnormal
      A S hSF hSsub hCS).trans hSB
  have hFBsolv : Group.IsSolvable (fittingSubgroupOf B) := by
    let : Group.IsNilpotent (fittingSubgroupOf B) :=
      fittingSubgroupOf_isNilpotent B
    infer_instance
  have hEAnormFB :
      componentLayerOf A ≤
        Subgroup.normalizer (fittingSubgroupOf B : Set G) :=
    hEAleB.trans
      (le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn B))
  have hEAFB : ⁅componentLayerOf A, fittingSubgroupOf B⁆ = ⊥ :=
    componentLayerOf_centralizes_solvable_of_le_normalizer
      A (fittingSubgroupOf B) hFB hFBsolv hEAnormFB
  have hEAleEB : componentLayerOf A ≤ componentLayerOf B := by
    rw [componentLayerOf]
    apply sSup_le
    intro K hK
    apply component_le_componentLayerOf_of_isDGroup_of_centralizes_fitting
      A B K hD hK
    · exact (le_sSup hK).trans hEAleB
    · apply le_antisymm
      · exact (Subgroup.commutator_mono (le_sSup hK) le_rfl).trans_eq hEAFB
      · exact bot_le
  have hcard : Nat.card (componentLayerOf B) =
      Nat.card (componentLayerOf A) := by
    dsimp [B]
    rw [componentLayerOf_conjugateSubgroup A g]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hEAeqEB : componentLayerOf A = componentLayerOf B :=
    Subgroup.eq_of_le_of_card_ge hEAleEB (Nat.le_of_eq hcard)
  rw [← hEAeqEB]
  exact (fstar_componentLayerOf_isNormalIn A).1

end CFSG.GorensteinWalter
