module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NoncommRing
import TauCeti.LinearAlgebra.Trace.Idempotent

public section

namespace CFSG.StandardType.GGKG3

theorem k3_trace_wrap (c : Matrix (Fin 6) (Fin 6) ℤ) (hc2 : c * c = 1)
    (h7 : ((c.trace : ℤ) : ZMod 7) = 2) : c.trace = 2 := by
  have h7' : ((c.trace : ℤ) : ZMod 7) = ((2 : ℤ) : ZMod 7) := by simpa using h7
  have hdvd : (((7 : ℕ) : ℤ)) ∣ (2 : ℤ) - c.trace :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ 7).1 h7'
  set N : Matrix (Fin 6) (Fin 6) ℚ := (Int.castRingHom ℚ).mapMatrix c with hN
  have hNN : N * N = 1 := by
    rw [hN, ← map_mul, hc2, map_one]
  set Q : Matrix (Fin 6) (Fin 6) ℚ := 1 + N with hQ
  have hQQ : Q * Q = (2 : ℚ) • Q := by
    calc Q * Q = 1 + 2 • N + N * N := by rw [hQ]; noncomm_ring
      _ = (2 : ℚ) • Q := by
        rw [hNN, hQ, ofNat_smul_eq_nsmul (R := ℚ)]
        abel
  set f := Matrix.toLin' Q with hf
  have hff : f * f = (2 : ℚ) • f := by
    rw [hf, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hQQ, map_smul]
  have htr := TauCeti.LinearMap.trace_eq_mul_finrank_range hff
  have hNtr : N.trace = (c.trace : ℚ) := by
    rw [hN]
    simp [Matrix.trace]
  rw [hf, Matrix.trace_toLin'_eq, hQ, Matrix.trace_add, Matrix.trace_one, Fintype.card_fin,
    hNtr] at htr
  have hr : Module.finrank ℚ (LinearMap.range f) ≤ 6 := by
    have := Submodule.finrank_le (LinearMap.range f)
    simpa using this
  have hint : (6 : ℤ) + c.trace = 2 * (Module.finrank ℚ (LinearMap.range f) : ℤ) := by
    have : ((6 : ℚ) + (c.trace : ℚ)) = 2 * (Module.finrank ℚ (LinearMap.range f) : ℚ) := by
      simpa using htr
    exact_mod_cast this
  omega

end CFSG.StandardType.GGKG3
