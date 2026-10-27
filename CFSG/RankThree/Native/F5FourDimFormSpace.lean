module

public import CFSG.RankThree.Native.F5MatrixArrays
import Certificates.Data.Kernel.U43Pk.Defs
import CFSG.Certificates.Kernel.ArrBfsCert
import CFSG.Certificates.Kernel.U43Pk.Sound
import CFSG.Certificates.Kernel.PackSetSound
import CFSG.Certificates.Kernel.SporSch.LyLoop
import CFSG.Certificates.Kernel.Bounds.LoadGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.RankThree.Native.DerivedGenerators
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.FieldTheory.Finite.Basic
public import Std.Data.HashMap

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open scoped Matrix

@[expose] def f5X : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 2, 2, 4, 2; 1, 4, 4, 0]

@[expose] def f5H : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, 1, 0, 0; 3, 1, 1, 0; 2, 2, 2, 0; 1, 1, 1, 4]

@[expose] def f5M : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, 1, 4, 1; 4, 0, 0, 2; 1, 0, 0, 1; 4, 3, 4, 0]

@[expose] def f5XU : GL (Fin 4) (ZMod 5) :=
  ⟨f5X, f5X ^ 4, by decide +kernel, by decide +kernel⟩

theorem f5M_det : f5M.det = 4 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, f5M, Matrix.submatrix]
  decide

theorem f5XU_val : ((f5XU : GL (Fin 4) (ZMod 5)) : Matrix (Fin 4) (Fin 4) (ZMod 5)) = f5X := rfl

theorem f5XU_pow_five : f5XU ^ 5 = 1 := Units.ext (by
  rw [Units.val_pow_eq_pow_val, f5XU_val]
  decide +kernel)

theorem f5XU_ne_one : f5XU ≠ 1 := fun h => by
  have := congrArg (fun u : GL (Fin 4) (ZMod 5) => (u : Matrix (Fin 4) (Fin 4) (ZMod 5))) h
  simp only [f5XU_val, Units.val_one] at this
  revert this
  decide +kernel

end CFSG.RankThree.Native
