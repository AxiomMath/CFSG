module

public import CFSG.LieType.Chevalley.C2E6ExteriorCubeKernel
public import CFSG.RankThree.GF2n.Smith81.S81A5Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type*} [Field K]

theorem rho_eq_cubeEnd (g : GL (Fin 6) K) :
    rho K g = CFSG.LieType.Chevalley.ExteriorCube.cubeEnd (g : Matrix (Fin 6) (Fin 6) K) := by
  rw [CFSG.LieType.Chevalley.ExteriorCube.cubeEnd_apply, Matrix.toLin'_apply']
  simp only [rho, TauCeti.extPowerRep, Representation.exteriorPower_apply, TauCeti.stdRep_apply]

theorem rho_mul (g g' : GL (Fin 6) K) : rho K (g * g') = rho K g * rho K g' := by
  simp only [rho_eq_cubeEnd, Units.val_mul, map_mul]

theorem rho_eq_one_iff (g : GL (Fin 6) K) :
    rho K g = 1 ↔ ∃ l : K, l ^ 3 = 1 ∧ (g : Matrix (Fin 6) (Fin 6) K) = l • 1 := by
  rw [rho_eq_cubeEnd]
  exact CFSG.LieType.Chevalley.ExteriorCube.cubeEnd_eq_one_iff _

theorem rho_smul (c : K) {g g' : GL (Fin 6) K}
    (h : (g' : Matrix (Fin 6) (Fin 6) K) = c • (g : Matrix (Fin 6) (Fin 6) K)) :
    rho K g' = c ^ 3 • rho K g := by
  have hM : (g' : Matrix (Fin 6) (Fin 6) K) =
      (c • (1 : Matrix (Fin 6) (Fin 6) K)) * (g : Matrix (Fin 6) (Fin 6) K) := by
    rw [h, smul_mul_assoc, one_mul]
  rw [rho_eq_cubeEnd, rho_eq_cubeEnd, hM, map_mul,
    CFSG.LieType.Chevalley.ExteriorCube.cubeEnd_smul_one, smul_mul_assoc, one_mul]

end CFSG.RankThree.GF2n.Smith81.A5Cube
