module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.TheoremA
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4 equation (10): the arithmetic Theorem-A transport

The group-theoretic PSL₂ constructor supplies two identities:

* the index-tower factorization
  `|H|index · (u p₀) = q k' · |M|index`, and
* the identification of the Bender--Glauberman parameter with the
  Section-4 parameters, `bg.k = k u p₀`.

This module performs the independent rational step from those identities and
`BenderGlauberman.theorem_A`.  Keeping this endpoint generic prevents the
eventual Section-4 structure module from encoding equation (10) as an
assumption.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Equation (10) follows from Theorem A and the two structural parameter
identities supplied by the PSL₂ Section-4 constructor. -/
public theorem secondCase_equation10_of_theorem_A
    {G : Type u} [Group G] [Finite G]
    (bg : BenderGlauberman.Hyp11 G)
    {q k k' u p0 m : ℚ}
    (hfactor : (bg.H.index : ℚ) * (u * p0) = q * k' * m)
    (hbgk : (bg.k : ℚ) = k * u * p0)
    (hu : 0 < u) (hp0 : 0 < p0) :
    q * k' * m ≤ 6 * k ^ 2 * u ^ 3 * p0 ^ 3 := by
  have hidxNat : 0 < bg.H.index := Nat.pos_of_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := bg.H))
  have hidx : (0 : ℚ) < (bg.H.index : ℚ) := by
    exact_mod_cast hidxNat
  have hA := (BenderGlauberman.theorem_A bg).1
  have hidxlt : (bg.H.index : ℚ) < 6 * (bg.k : ℚ) ^ 2 := by
    apply (lt_div_iff₀ hidx).mp at hA
    nlinarith
  rw [← hfactor]
  rw [hbgk] at hidxlt
  have hmul : (u * p0) * (bg.H.index : ℚ) ≤
      (u * p0) * (6 * (k * u * p0) ^ 2) := by
    apply mul_le_mul_of_nonneg_left (le_of_lt hidxlt)
    positivity
  nlinarith

end CFSG.GorensteinWalter
