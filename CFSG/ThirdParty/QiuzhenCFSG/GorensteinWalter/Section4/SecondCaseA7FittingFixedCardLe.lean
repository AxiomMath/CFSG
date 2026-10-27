module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7FittingFixedTI
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseConjugator
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFittingCyclicCardLe
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Cardinality of the A7 fitting fixed part

The outside normalizer and the A7 trivial-intersection theorem supply the
two hypotheses needed by the generic equation-(6) cardinal transfer.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The equation-(3) fixed part is cyclic and no larger than its inverted
factor. -/
public theorem secondCase_a7_fitting_fixed_cyclic_and_card_le
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7)
    (K0 F : Subgroup G)
    (hK0cyc : IsCyclic K0)
    (hFleFU : F ≤ fittingSubgroupOf c.U)
    (hFnormalM : IsNormalIn F w.M)
    (hFcentE : F ≤ Subgroup.centralizer (d.E : Set G))
    (hjoin : K0 ⊔ F = fittingSubgroupOf c.U ⊓ w.M) :
    IsCyclic F ∧ Nat.card F ≤ Nat.card K0 := by
  let Y : Subgroup G := fittingSubgroupOf c.U ⊓ w.M
  obtain ⟨g, hgY, hgnotM⟩ := secondCase_exists_conjugator_not_mem_M hmin c w
  have hFleM : F ≤ w.M := hFnormalM.1
  have hFleY : F ≤ Y := by
    intro f hf
    exact ⟨hFleFU hf, hFleM hf⟩
  have hFnormalY : IsNormalIn F Y := by
    refine ⟨hFleY, ?_⟩
    intro y hy f hf
    exact hFnormalM.2 y hy.2 f hf
  have hdisj : F ⊓ conjugateSubgroup F g = ⊥ :=
    secondCase_a7_fitting_fixed_TI
      hmin c w d hA7 hmodel F hFleFU hFleM hFcentE g hgnotM
  exact secondCase_fitting_fixed_part_cyclic_and_card_le_of_conjugate_disjoint
    K0 F Y hK0cyc hFnormalY (by simpa [Y] using hjoin) g
      (by simpa [Y] using hgY) hdisj

end CFSG.GorensteinWalter
