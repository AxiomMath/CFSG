module

import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Degree arithmetic in the Brauer--Suzuki--Wall argument

The last character calculation reduces Bender's order formula to an integer
square.  This module isolates that purely arithmetic endpoint.
-/

namespace CFSG.GorensteinWalter

/-- If the three signed character degrees satisfy Bender's degree, index, and
class-multiplication equations, then the index has one of the two required
Brauer--Suzuki--Wall values. -/
public theorem brauerSuzukiWall_index_cases_of_degree_equations
    (k n : ℕ) (gamma lambda : ℤ)
    (hk : 4 < k)
    (hn : 0 < n)
    (hdegree : 1 + gamma - lambda = 0)
    (hindex : 2 * (n : ℤ) = gamma * lambda)
    (hmain :
      2 * (k : ℤ) ^ 2 * gamma * lambda =
        (n : ℤ) * (gamma * lambda + 4 * lambda - gamma)) :
    n = (2 * k + 1) * (k + 1) ∨
      n = (2 * k - 1) * (k - 1) := by
  have hnInt : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hn
  have hfactor :
      gamma * lambda + 4 * lambda - gamma = 4 * (k : ℤ) ^ 2 := by
    nlinarith [hindex, hmain]
  have hgamma : gamma = lambda - 1 := by
    linarith [hdegree]
  have hsquare : (lambda + 1) ^ 2 = (2 * (k : ℤ)) ^ 2 := by
    rw [hgamma] at hfactor
    nlinarith [hfactor]
  rcases eq_or_eq_neg_of_sq_eq_sq (lambda + 1) (2 * (k : ℤ)) hsquare with
      hplus | hminus
  · right
    have hindexInt :
        (n : ℤ) = (2 * (k : ℤ) - 1) * ((k : ℤ) - 1) := by
      rw [hgamma] at hindex
      nlinarith [hplus, hindex]
    have hkOne : 1 ≤ k := by omega
    have htwoKOne : 1 ≤ 2 * k := by omega
    exact_mod_cast hindexInt
  · left
    have hindexInt :
        (n : ℤ) = (2 * (k : ℤ) + 1) * ((k : ℤ) + 1) := by
      rw [hgamma] at hindex
      nlinarith [hminus, hindex]
    exact_mod_cast hindexInt

end CFSG.GorensteinWalter
