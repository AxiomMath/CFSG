module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

public section

namespace CFSG.RankThree.PartTwo.Sec15.KL3FactsProof

open Matrix

variable {K : Type} [Field K]

theorem exists_scalar_of_mk_commute {g t : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk g * ProjGenLinGroup.mk t =
      ProjGenLinGroup.mk t * ProjGenLinGroup.mk g) :
    ∃ μ : Kˣ, g * t * g⁻¹ = GeneralLinearGroup.scalar (Fin 3) μ * t := by
  have h1 : ProjGenLinGroup.mk (g * t * g⁻¹ * t⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h, mul_inv_cancel_right, mul_inv_cancel]
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
  obtain ⟨μ, hμ⟩ := h1
  refine ⟨μ, ?_⟩
  rw [hμ]
  group

end CFSG.RankThree.PartTwo.Sec15.KL3FactsProof
