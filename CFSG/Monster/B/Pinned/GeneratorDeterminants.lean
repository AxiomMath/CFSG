
module

public import CFSG.Monster.B.Pinned.GeneratorDeterminantsBase
import all CFSG.Monster.B.Pinned.GeneratorDeterminantsBase

public import Certificates.Certificate3109

public section

namespace CFSG.Monster.B

open CFSG.Blueprint

theorem genA₁_mul_self : genA₁ * genA₁ = 1 :=
  Certificates.certificate3109.1

theorem genA₂_cube : genA₂ * genA₂ * genA₂ = 1 :=
  Certificates.certificate3109.2

theorem B_generator_determinants :
    genA₁.det = 1 ∧ genA₂.det = 1 ∧ IsUnit genA₁ ∧ IsUnit genA₂ := by
  have h1 : genA₁.det = 1 := by
    have e := congrArg Matrix.det genA₁_mul_self
    rw [Matrix.det_mul, Matrix.det_one, ← pow_two] at e
    exact zmod_two_eq_one_of_pow e
  have h2 : genA₂.det = 1 := by
    have e := congrArg Matrix.det genA₂_cube
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one, ← pow_two, ← pow_succ] at e
    exact zmod_two_eq_one_of_pow e
  refine ⟨h1, h2, ?_, ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det _).2 (h1 ▸ isUnit_one)
  · exact (Matrix.isUnit_iff_isUnit_det _).2 (h2 ▸ isUnit_one)

end CFSG.Monster.B
