module

public import CFSG.LocalAnalysis.SignalizerFunctor.FittingCore

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType]

theorem nilpotent_subgroup_of_commutator_le_center (target : Subgroup GroupType)
    (central : ⁅target, target⁆ ≤ Subgroup.center GroupType) : Group.IsNilpotent target := by
  apply Group.IsNilpotent.mk
  refine ⟨2, top_unique ?_⟩
  intro element _
  apply Subgroup.mem_upperCentralSeries_succ_iff.mpr
  intro other
  rw [Subgroup.upperCentralSeries_one]
  apply Subgroup.mem_center_iff.mpr
  intro third
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp
    (central (Subgroup.commutator_mem_commutator element.property other.property)) third.val

theorem fitting_centralizer_characteristic :
    (Subgroup.centralizer (fittingSubgroup (GroupType := GroupType) : Set GroupType)).Characteristic := by
  let := fitting_subgroup_characteristic (GroupType := GroupType)
  infer_instance

theorem solvable_fitting_centralizer_le [Group.IsSolvable GroupType] :
    Subgroup.centralizer (fittingSubgroup (GroupType := GroupType) : Set GroupType) ≤ fittingSubgroup := by
  let centralizer := Subgroup.centralizer (fittingSubgroup (GroupType := GroupType) : Set GroupType)
  let _characteristic : centralizer.Characteristic := fitting_centralizer_characteristic
  have step : ∀ index : ℕ, derivedSeries centralizer (index + 1) ≤ Subgroup.center centralizer →
      derivedSeries centralizer index ≤ Subgroup.center centralizer := by
    intro index next_central
    let internal := derivedSeries centralizer index
    have nilpotent : Group.IsNilpotent internal := by
      apply nilpotent_subgroup_of_commutator_le_center
      exact (derivedSeries_succ centralizer index).symm.le.trans next_central
    let _internalCharacteristic : internal.Characteristic := inferInstance
    let embedded := internal.map centralizer.subtype
    let _embeddedCharacteristic : embedded.Characteristic := inferInstance
    have embedded_le : embedded ≤ fittingSubgroup := fitting_subgroup_contains embedded inferInstance
      (by let := nilpotent; exact Group.nilpotent_of_mulEquiv
            (internal.equivMapOfInjective centralizer.subtype centralizer.subtype_injective))
    intro element member
    apply Subgroup.mem_center_iff.mpr
    intro other
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp other.property element.val
      (embedded_le (Subgroup.mem_map_of_mem centralizer.subtype member))).symm
  have descend : ∀ distance index : ℕ,
      derivedSeries centralizer (index + distance) ≤ Subgroup.center centralizer →
      derivedSeries centralizer index ≤ Subgroup.center centralizer := by
    intro distance
    induction distance with
    | zero =>
      intro index central
      exact central
    | succ distance induction_hypothesis =>
      intro index central
      apply step index
      apply induction_hypothesis (index + 1)
      simpa only [Nat.add_assoc, Nat.add_comm distance 1] using central
  obtain ⟨depth, trivial⟩ := Group.IsSolvable.solvable (G := centralizer)
  have whole_central : (⊤ : Subgroup centralizer) ≤ Subgroup.center centralizer := by
    rw [← derivedSeries_zero centralizer]
    apply descend depth 0
    rw [zero_add, trivial]
    exact bot_le
  have commutative : IsMulCommutative centralizer := by
    apply (commutator_eq_bot_iff centralizer).mp
    exact (commutator_eq_bot_iff_center_eq_top centralizer).mpr (top_unique whole_central)
  let := commutative
  let _commGroup : CommGroup centralizer := { centralizer.toGroup with mul_comm := mul_comm' }
  exact fitting_subgroup_contains centralizer inferInstance inferInstance

end CFSG.SignalizerFunctor.Helpers
