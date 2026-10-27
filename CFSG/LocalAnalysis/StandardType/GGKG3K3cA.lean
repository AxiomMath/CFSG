module

public import CFSG.LocalAnalysis.StandardType.GGKG3ExData

public section

namespace CFSG.StandardType.GGKG3

open CFSG.StandardType.GGKG3.K3dCheck

private def kg3_f : ℤ →+* ZMod 7 := Int.castRingHom (ZMod 7)

private def kg3_C7 : Matrix (Fin 6) (Fin 6) (ZMod 7) :=
  (Matrix.of kC).map kg3_f

private def kg3_Ci : Matrix (Fin 6) (Fin 6) (ZMod 7) :=
  (5 : ZMod 7) • (Matrix.of kAdjC).map kg3_f

private def kg3_e2 : Matrix (Fin 6) (Fin 6) (ZMod 7) :=
  (3 : ZMod 7) • (k3M7 - (4 : ZMod 7) • (1 : Matrix (Fin 6) (Fin 6) (ZMod 7)))

private def kg3_e4 : Matrix (Fin 6) (Fin 6) (ZMod 7) :=
  (3 : ZMod 7) • (k3M7 * k3M7 - (4 : ZMod 7) • (1 : Matrix (Fin 6) (Fin 6) (ZMod 7)))

private theorem kg3_Ci_mul_C7 : kg3_Ci * kg3_C7 = 1 := by decide +kernel
private theorem kg3_C7_mul_Ci : kg3_C7 * kg3_Ci = 1 := by decide +kernel
private theorem kg3_e2_add_e4 : kg3_e2 + kg3_e4 = 1 := by decide +kernel
private theorem kg3_e2t_mul_C7 : kg3_e2.transpose * kg3_C7 = kg3_C7 * kg3_e4 := by decide +kernel
private theorem kg3_e2t : kg3_e2.transpose = k3Q := by decide +kernel

theorem k3_trace_double (c : Matrix (Fin 6) (Fin 6) ℤ)
    (hcC : c.transpose * Matrix.of kC * c = Matrix.of kC) (hc2 : c * c = 1) :
    ((c.trace : ℤ) : ZMod 7) =
      2 * (k3Q * (c.map (Int.castRingHom (ZMod 7))).transpose).trace := by
  have hcbar2 : (c.map kg3_f) * (c.map kg3_f) = 1 := by
    rw [← Matrix.map_mul, hc2]
    exact Matrix.map_one kg3_f (map_zero _) (map_one _)
  have horth : (c.map kg3_f).transpose * kg3_C7 * (c.map kg3_f) = kg3_C7 := by
    have h := congrArg (fun M => M.map kg3_f) hcC
    simpa [Matrix.map_mul, Matrix.transpose_map, kg3_C7] using h
  have hctC : (c.map kg3_f).transpose * kg3_C7 = kg3_C7 * (c.map kg3_f) := by
    have h := congrArg (fun X => X * (c.map kg3_f)) horth
    rwa [mul_assoc, hcbar2, mul_one] at h
  have hkey : kg3_C7 * ((c.map kg3_f) * kg3_e4) =
      (kg3_e2 * (c.map kg3_f)).transpose * kg3_C7 := by
    calc kg3_C7 * ((c.map kg3_f) * kg3_e4)
        = (kg3_C7 * (c.map kg3_f)) * kg3_e4 := by rw [mul_assoc]
      _ = ((c.map kg3_f).transpose * kg3_C7) * kg3_e4 := by rw [← hctC]
      _ = (c.map kg3_f).transpose * (kg3_C7 * kg3_e4) := by rw [mul_assoc]
      _ = (c.map kg3_f).transpose * (kg3_e2.transpose * kg3_C7) := by
            rw [← kg3_e2t_mul_C7]
      _ = ((c.map kg3_f).transpose * kg3_e2.transpose) * kg3_C7 := by
            rw [mul_assoc]
      _ = (kg3_e2 * (c.map kg3_f)).transpose * kg3_C7 := by
            rw [Matrix.transpose_mul]
  have htrace_eq : ((c.map kg3_f) * kg3_e4).trace =
      ((c.map kg3_f) * kg3_e2).trace := by
    calc ((c.map kg3_f) * kg3_e4).trace
        = (kg3_Ci * (kg3_C7 * ((c.map kg3_f) * kg3_e4))).trace := by
            rw [← mul_assoc, kg3_Ci_mul_C7, one_mul]
      _ = (kg3_Ci * ((kg3_e2 * (c.map kg3_f)).transpose * kg3_C7)).trace := by
            rw [hkey]
      _ = (((kg3_e2 * (c.map kg3_f)).transpose * kg3_C7) * kg3_Ci).trace := by
            rw [Matrix.trace_mul_comm]
      _ = ((kg3_e2 * (c.map kg3_f)).transpose * (kg3_C7 * kg3_Ci)).trace := by
            rw [mul_assoc]
      _ = ((kg3_e2 * (c.map kg3_f)).transpose).trace := by
            rw [kg3_C7_mul_Ci, mul_one]
      _ = ((c.map kg3_f) * kg3_e2).trace := by
            rw [Matrix.trace_transpose, Matrix.trace_mul_comm]
  have hsplit : (c.map kg3_f).trace =
      ((c.map kg3_f) * kg3_e2).trace + ((c.map kg3_f) * kg3_e4).trace := by
    calc (c.map kg3_f).trace
        = ((c.map kg3_f) * 1).trace := by rw [mul_one]
      _ = ((c.map kg3_f) * (kg3_e2 + kg3_e4)).trace := by rw [kg3_e2_add_e4]
      _ = ((c.map kg3_f) * kg3_e2 + (c.map kg3_f) * kg3_e4).trace := by rw [mul_add]
      _ = ((c.map kg3_f) * kg3_e2).trace + ((c.map kg3_f) * kg3_e4).trace := by
            rw [Matrix.trace_add]
  have hstep : ((c.map kg3_f) * kg3_e2).trace =
      (k3Q * (c.map kg3_f).transpose).trace := by
    calc ((c.map kg3_f) * kg3_e2).trace
        = (((c.map kg3_f) * kg3_e2).transpose).trace := by
            rw [Matrix.trace_transpose]
      _ = (kg3_e2.transpose * (c.map kg3_f).transpose).trace := by
            rw [Matrix.transpose_mul]
      _ = (k3Q * (c.map kg3_f).transpose).trace := by rw [kg3_e2t]
  have hfinal : (c.map kg3_f).trace =
      2 * (k3Q * (c.map kg3_f).transpose).trace := by
    rw [hsplit, htrace_eq, hstep]
    ring
  have hcast : ((c.trace : ℤ) : ZMod 7) = (c.map kg3_f).trace :=
    AddMonoidHom.map_trace kg3_f c
  simpa [kg3_f] using hcast.trans hfinal

end CFSG.StandardType.GGKG3
