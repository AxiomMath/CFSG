module

public import CFSG.Fischer.Classification.Unitary.Basic
import all CFSG.Fischer.F4

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4PSU

open Matrix CFSG.Fischer

@[expose] def swapCommA : Matrix (Fin 3) (Fin 3) F4 :=
  !![1, F4.ω, 1; F4.ω, 1, 1; F4.ω, F4.ω, F4.ω ^ 2]

@[expose] def swapCommB : Matrix (Fin 3) (Fin 3) F4 :=
  !![1, F4.ω, F4.ω; F4.ω, 1, F4.ω; 1, 1, F4.ω ^ 2]

@[expose] def swapZeroOne : Matrix (Fin 3) (Fin 3) F4 :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem swapCommA_unitary : (swapCommA.map (· ^ 2))ᵀ * swapCommA = 1 := by decide

theorem swapCommB_unitary : (swapCommB.map (· ^ 2))ᵀ * swapCommB = 1 := by decide

theorem det_swapCommA : swapCommA.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

theorem det_swapCommB : swapCommB.det = 1 := by
  rw [Matrix.det_fin_three]
  decide

theorem swapCommA_mul_swapCommB :
    swapCommA * swapCommB = swapZeroOne * swapCommB * swapCommA := by decide

theorem omega_sq : Classification.Unitary.ω ^ 2 = Classification.Unitary.ω + 1 := by
  rw [Classification.Unitary.omega_eq, ← map_pow, (by decide : F4.ω ^ 2 = F4.ω + 1), map_add,
    map_one]

theorem omega_cube : Classification.Unitary.ω ^ 3 = 1 := by
  rw [Classification.Unitary.omega_eq, ← map_pow, (by decide : F4.ω ^ 3 = 1), map_one]

end CFSG.RankThree.GF2n.Stroth78.Sec4PSU
