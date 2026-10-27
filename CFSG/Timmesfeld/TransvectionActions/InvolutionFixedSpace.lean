module


public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.Timmesfeld.TransvectionActions

variable {Space : Type*} [AddCommGroup Space] [Module (ZMod 2) Space]

theorem finrank_le_two_mul_finrank_ker_involution [Module.Finite (ZMod 2) Space]
    (linearAction : Space →ₗ[ZMod 2] Space)
    (involutive : ∀ vector, linearAction (linearAction vector) = vector) :
    Module.finrank (ZMod 2) Space ≤
      2 * Module.finrank (ZMod 2) (LinearMap.ker (linearAction - LinearMap.id)) := by
  have rankNullity := LinearMap.finrank_range_add_finrank_ker (linearAction - LinearMap.id)
  have rangeBound : LinearMap.range (linearAction - LinearMap.id) ≤
      LinearMap.ker (linearAction - LinearMap.id) := by
    rintro _ ⟨vector, rfl⟩
    have doubledDifference : (2 : ZMod 2) • (vector - linearAction vector) = 0 := by
      rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]
    rw [two_smul] at doubledDifference
    change (linearAction - LinearMap.id : Space →ₗ[ZMod 2] Space)
      ((linearAction - LinearMap.id : Space →ₗ[ZMod 2] Space) vector) = 0
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, involutive]
    rw [← doubledDifference]
    abel
  have rangeRankBound := Submodule.finrank_mono rangeBound
  omega

end CFSG.Timmesfeld.TransvectionActions
