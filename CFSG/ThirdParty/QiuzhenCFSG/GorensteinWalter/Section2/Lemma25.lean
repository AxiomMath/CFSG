module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma25Assembly
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma25ComponentLayer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma25PGroup

namespace CFSG
end CFSG
open CFSG

/-!
# Gorenstein--Walter Lemma 2.5

The proof splits according to whether `F*(Hhat)` is a `p`-group.  The
`p`-group branch is Lemma 2.4.  Otherwise the control core first puts the
Fitting subgroup and then the component layer of the controlled conjugate
inside `Hhat`; Bender 1.7(iii) then forces equality.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Lemma 2.5: a controlled conjugate of `Hhat` is equal to `Hhat` when its
odd core is nontrivial. -/
public theorem lemma_2_5
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (g : G)
    (hcontrol : NormalizerControlledBy c.Hhat (conjugateSubgroup c.Hhat g))
    (hodd : oddCoreOf c.Hhat ≠ ⊥) :
    c.Hhat = conjugateSubgroup c.Hhat g := by
  by_cases hP : ∃ p : ℕ, p.Prime ∧
      IsPGroup p (generalizedFittingSubgroupOf c.Hhat)
  · rcases hP with ⟨p, hp, hAp⟩
    exact eq_conjugateSubgroup_of_controlled_conjugate_of_oddCore_ne_bot_of_isPGroup
      hmin c g hcontrol hodd hp hAp
  · have hnp : ∀ p : ℕ, p.Prime →
        ¬ IsPGroup p (generalizedFittingSubgroupOf c.Hhat) := by
      intro p hp hAp
      exact hP ⟨p, hp, hAp⟩
    have hC : ControlCore c.Hhat (conjugateSubgroup c.Hhat g) :=
      controlCore_of_normalizerControlledBy hcontrol
    have hFB : fittingSubgroupOf (conjugateSubgroup c.Hhat g) ≤ c.Hhat :=
      fittingSubgroupOf_conjugateSubgroup_le_of_controlCore_of_not_isPGroup
        (minimalCounterexample_isSimple hmin) c.Hhat c.Hhat_maximal g hC hnp
    have hEB : componentLayerOf (conjugateSubgroup c.Hhat g) ≤ c.Hhat :=
      componentLayerOf_conjugateSubgroup_le_of_minimalCounterexample_of_controlCore_of_fitting_le
        hmin c.Hhat c.Hhat_maximal g hC hFB
    exact eq_conjugateSubgroup_of_controlCore_of_not_isPGroup_of_componentLayer_le
      (minimalCounterexample_isSimple hmin) c.Hhat c.Hhat_maximal g hC hnp hEB

end CFSG.GorensteinWalter
