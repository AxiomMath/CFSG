module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

namespace CFSG
end CFSG
open CFSG

/-!
# Injectivity of the dimension-two projective linear map
-/

namespace CFSG.GorensteinWalter

universe u v

/-- An injective field homomorphism induces an injective map on
dimension-two projective general linear groups. -/
public theorem pgl2_map_injective_of_injective
    {R : Type u} {S : Type v} [Field R] [Field S]
    (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective
      (Matrix.ProjGenLinGroup.map (n := Fin 2) f) := by
  have hGL : Function.Injective
      (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
    apply Units.map_injective
    exact Matrix.map_injective hf
  intro x y hxy
  induction x using Matrix.ProjGenLinGroup.induction_on with
  | mk A =>
      induction y using Matrix.ProjGenLinGroup.induction_on with
      | mk B =>
          apply QuotientGroup.eq_iff_div_mem.mpr
          have hcentS :
              Matrix.GeneralLinearGroup.map (n := Fin 2) f (A / B) ∈
                Subgroup.center (GL (Fin 2) S) := by
            rw [map_div]
            exact QuotientGroup.eq_iff_div_mem.mp hxy
          rw [Subgroup.mem_center_iff]
          intro C
          apply hGL
          rw [map_mul, map_mul]
          exact Subgroup.mem_center_iff.mp hcentS
            (Matrix.GeneralLinearGroup.map (n := Fin 2) f C)

end CFSG.GorensteinWalter
