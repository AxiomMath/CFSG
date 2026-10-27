module


public import CFSG.Timmesfeld.TransvectionActions.Basic


public section

namespace CFSG.Timmesfeld.TransvectionActions

variable {ActingGroup : Type*} [Group ActingGroup] {Space : Type*}
  [AddCommGroup Space] [Module (ZMod 2) Space]
  {action : Representation (ZMod 2) ActingGroup Space} {center : Space}

theorem CommonTransvectionCenter.ne_zero (commonCenter : CommonTransvectionCenter action center) :
    center ≠ 0 := by
  unfold CommonTransvectionCenter at commonCenter
  exact commonCenter.1

@[expose] noncomputable def displacementFunctional
    (commonCenter : CommonTransvectionCenter action center) (element : ActingGroup) :
    Module.Dual (ZMod 2) Space :=
  (LinearEquiv.coord (ZMod 2) Space center commonCenter.ne_zero).toLinearMap ∘ₗ
    (displacement action element).codRestrict (Submodule.span (ZMod 2) {center}) (by
      intro vector
      have rangeBound : LinearMap.range (displacement action element) ≤
          Submodule.span (ZMod 2) {center} := by
        by_cases elementOne : element = 1
        · subst element
          have displacementOne : displacement action (1 : ActingGroup) = 0 := by
            ext vector
            simp [displacement_apply]
          rw [displacementOne]
          simp
        · exact (commonCenter.2 element elementOne).le
      exact rangeBound ⟨vector, rfl⟩)

theorem displacementFunctional_smul (commonCenter : CommonTransvectionCenter action center)
    (element : ActingGroup) (vector : Space) :
    displacementFunctional commonCenter element vector • center = action element vector - vector := by
  have rangeBound : LinearMap.range (displacement action element) ≤
      Submodule.span (ZMod 2) {center} := by
    by_cases elementOne : element = 1
    · subst element
      have displacementOne : displacement action (1 : ActingGroup) = 0 := by
        ext vector
        simp [displacement_apply]
      rw [displacementOne]
      simp
    · exact (commonCenter.2 element elementOne).le
  have coordinateIdentity := LinearEquiv.coord_apply_smul (ZMod 2) Space center commonCenter.ne_zero
    ⟨displacement action element vector, rangeBound ⟨vector, rfl⟩⟩
  simpa [displacementFunctional, displacement_apply] using coordinateIdentity

theorem displacementFunctional_center (commonCenter : CommonTransvectionCenter action center)
    (elementary : IsElementaryAbelian2 ActingGroup) (element : ActingGroup) :
    displacementFunctional commonCenter element center = 0 := by
  have centerFixed : action element center = center := by
    by_cases elementOne : element = 1
    · subst element
      simp
    · have centerInRange : center ∈ LinearMap.range (displacement action element) := by
        rw [commonCenter.2 element elementOne]
        exact Submodule.mem_span_singleton_self center
      obtain ⟨vector, displacementVector⟩ := centerInRange
      rw [displacement_apply] at displacementVector
      have doubledDifference : (2 : ZMod 2) • (vector - action element vector) = 0 := by
        rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
      rw [two_smul] at doubledDifference
      have squareAction : action element (action element vector) = vector := by
        have actionProduct : action element (action element vector) =
            action (element * element) vector := by
          rw [map_mul]
          rfl
        rw [actionProduct, ← sq, elementary.2 element]
        simp
      rw [← displacementVector, map_sub, squareAction]
      rw [← sub_eq_zero, ← doubledDifference]
      abel
  have coefficientIdentity := displacementFunctional_smul commonCenter element center
  rw [centerFixed, sub_self] at coefficientIdentity
  exact (smul_eq_zero.mp coefficientIdentity).resolve_right commonCenter.ne_zero

theorem displacementFunctional_mul (commonCenter : CommonTransvectionCenter action center)
    (elementary : IsElementaryAbelian2 ActingGroup) (first second : ActingGroup) :
    displacementFunctional commonCenter (first * second) =
      displacementFunctional commonCenter first + displacementFunctional commonCenter second := by
  ext vector
  apply smul_left_injective (ZMod 2) commonCenter.ne_zero
  dsimp only
  have secondDisplacement := displacementFunctional_smul commonCenter second vector
  have firstDisplacement := displacementFunctional_smul commonCenter first (action second vector)
  have secondAction : action second vector =
      vector + displacementFunctional commonCenter second vector • center := by
    rw [secondDisplacement]
    abel
  have firstCoefficient : displacementFunctional commonCenter first (action second vector) =
      displacementFunctional commonCenter first vector := by
    rw [secondAction, map_add, map_smul, displacementFunctional_center commonCenter elementary,
      smul_zero, add_zero]
  rw [firstCoefficient] at firstDisplacement
  have actionProduct : action first (action second vector) = action (first * second) vector := by
    rw [map_mul]
    rfl
  rw [displacementFunctional_smul, LinearMap.add_apply, add_smul, firstDisplacement,
    secondDisplacement, actionProduct]
  abel

theorem displacementFunctional_one (commonCenter : CommonTransvectionCenter action center) :
    displacementFunctional commonCenter (1 : ActingGroup) = 0 := by
  ext vector
  apply smul_left_injective (ZMod 2) commonCenter.ne_zero
  dsimp only
  rw [displacementFunctional_smul]
  simp

@[expose] noncomputable def displacementHom (commonCenter : CommonTransvectionCenter action center)
    (elementary : IsElementaryAbelian2 ActingGroup) :
    ActingGroup →* Multiplicative (Module.Dual (ZMod 2) Space) where
  toFun element := Multiplicative.ofAdd (displacementFunctional commonCenter element)
  map_one' := by simp [displacementFunctional_one commonCenter]
  map_mul' first second := by simp [displacementFunctional_mul commonCenter elementary]

theorem displacementHom_injective (commonCenter : CommonTransvectionCenter action center)
    (elementary : IsElementaryAbelian2 ActingGroup) :
    Function.Injective (displacementHom commonCenter elementary) := by
  rw [injective_iff_map_eq_one]
  intro element imageOne
  have coefficientZero : displacementFunctional commonCenter element = 0 := by
    simpa [displacementHom] using imageOne
  by_contra elementNotOne
  have centerInRange : center ∈ LinearMap.range (displacement action element) := by
    rw [commonCenter.2 element elementNotOne]
    exact Submodule.mem_span_singleton_self center
  obtain ⟨vector, displacementVector⟩ := centerInRange
  have coefficientIdentity := displacementFunctional_smul commonCenter element vector
  rw [coefficientZero, LinearMap.zero_apply, zero_smul, eq_comm, sub_eq_zero] at coefficientIdentity
  rw [displacement_apply, coefficientIdentity, sub_self] at displacementVector
  exact commonCenter.ne_zero displacementVector.symm

@[expose] noncomputable def displacementImage (commonCenter : CommonTransvectionCenter action center)
    (elementary : IsElementaryAbelian2 ActingGroup) : Submodule (ZMod 2) (Module.Dual (ZMod 2) Space) where
  carrier := Set.range (displacementFunctional commonCenter)
  add_mem' := by
    rintro _ _ ⟨first, rfl⟩ ⟨second, rfl⟩
    exact ⟨first * second, displacementFunctional_mul commonCenter elementary first second⟩
  zero_mem' := ⟨1, displacementFunctional_one commonCenter⟩
  smul_mem' := by
    intro scalar functional functionalMem
    have scalarCases : scalar = 0 ∨ scalar = 1 := by revert scalar; decide
    rcases scalarCases with rfl | rfl
    · rw [zero_smul]
      exact ⟨1, displacementFunctional_one commonCenter⟩
    · rw [one_smul]
      exact functionalMem

theorem mem_displacementImage (commonCenter : CommonTransvectionCenter action center)
    (elementary : IsElementaryAbelian2 ActingGroup) (functional : Module.Dual (ZMod 2) Space) :
    functional ∈ displacementImage commonCenter elementary ↔
      ∃ element, displacementFunctional commonCenter element = functional := Iff.rfl

end CFSG.Timmesfeld.TransvectionActions
