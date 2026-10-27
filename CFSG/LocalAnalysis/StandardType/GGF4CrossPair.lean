module

public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreRep
public import CFSG.LocalAnalysis.StandardType.GGF4WeylQuad
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG.StandardType.F4Model

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

theorem inv_eq_self_of_isRefl {t : W} (ht : R.IsRefl t) : t⁻¹ = t := by
  obtain ⟨g, j, rfl⟩ := ht
  rw [mul_inv_rev, mul_inv_rev, inv_inv, R.s_inv j, mul_assoc]

theorem orderOf_eq_four_of_ord4b {u v : W} {x y : M4} (hu : R.ρ u = x.toMat)
    (hv : R.ρ v = y.toMat) (h : ord4b x y = true) : orderOf (u * v) = 4 := by
  simp only [ord4b, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
  have hρ : R.ρ (u * v) = (x.mul y).toMat := R.rho_mul hu hv
  have h4 : (u * v) ^ 2 ^ (1 + 1) = 1 := by
    apply R.inj
    rw [map_pow, hρ, map_one, show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, sq, sq,
      ← M4.toMat_mul, ← M4.toMat_mul]
    change (pw4 (x.mul y)).toMat = 1
    rw [h.1, M4.toMat_one]
  have h2 : ¬ (u * v) ^ 2 ^ 1 = 1 := by
    intro h2
    apply h.2
    apply M4.toMat_injective
    have h2' := congrArg R.ρ h2
    rw [map_pow, hρ, map_one, pow_one, sq, ← M4.toMat_mul] at h2'
    change (pw2 (x.mul y)).toMat = M4.one.toMat
    rw [M4.toMat_one]
    exact h2'
  have := orderOf_eq_prime_pow (p := 2) h2 h4
  simpa using this

end F4Rep

end CFSG.StandardType.F4Model

end
