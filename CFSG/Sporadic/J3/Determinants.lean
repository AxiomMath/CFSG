module

public import Certificates.Data.CFSGNative.J3.Data
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.J3

open CFSG.Blueprint.NativeSporadic

private theorem seedA_eq : Native.seedA = J3Seed1 := rfl

private theorem seedB_eq : Native.seedB = J3Seed2 := rfl

private theorem det_ne_zero_of_pow {M : Matrix (Fin 80) (Fin 80) (ZMod 2)} {e : ℕ} (he : e ≠ 0)
    (h : M ^ e = 1) : M.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_pow, h0, zero_pow he, Matrix.det_one] at this
  exact zero_ne_one this

end CFSG.Sporadic.J3
