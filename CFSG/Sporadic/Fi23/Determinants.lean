module

public import CFSG.F3.Spec
public import Certificates.Certificate9000
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.NativeSporadic CFSG.F3.Native

theorem rows_B_cube :
    eqM 253 (powM 253 (rowsOf 253 Native.seedB) 3) (idM 253) = true := by
  exact Certificates.certificate9000.1

private theorem seedA_eq : Native.seedA = Fi23Seed1 := rfl

private theorem seedB_eq : Native.seedB = Fi23Seed2 := rfl

private theorem mul_size (X Y : Array V) : (mul 253 X Y).size = X.size := by
  unfold mul; simp

private theorem idM_size : (idM 253).size = 253 := by
  unfold idM; simp

private theorem powM_size (M : Array V) (e : ℕ) : (powM 253 M e).size = 253 := by
  induction e with
  | zero => exact idM_size
  | succ e ih => rw [powM, mul_size, ih]

private theorem RowsWF.powM {M : Array V} (hM : RowsWF M) (e : ℕ) : RowsWF (powM 253 M e) := by
  induction e with
  | zero => exact RowsWF.idM 253
  | succ e ih => exact RowsWF.mul _ 253 ih hM

private theorem toMat_powM {M : Array V} (hM : RowsWF M) (e : ℕ) :
    toMat 253 (powM 253 M e) = toMat 253 M ^ e := by
  induction e with
  | zero => rw [pow_zero]; exact toMat_idM 253
  | succ e ih =>
    rw [CFSG.F3.Native.powM, toMat_mul (powM_size M e) (RowsWF.powM hM e) hM, ih, pow_succ]

end CFSG.Sporadic.Fi23
