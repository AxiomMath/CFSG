module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseReflection
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: rational parameter package for the linear contradiction

This module owns the rational parameter package consumed by
`secondCase_linearArithmetic`.

The missing group-theoretic step is a theorem

```lean
theorem secondCase_linearParameters
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hKprimePower : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (hmodel : d.model = ComponentQuotientModel.projectiveSpecialLinear
      K hKprimePower e) :
    SecondCaseLinearParameters
```

That theorem requires the equations-(1)--(9) Section-4 structure module
(`SecondCaseStructure`) plus equation (10) from
`BenderGlauberman.theorem_A` and equation (11) from the conjugate count;
the exact statement is recorded in `/tmp/s4-linear-parameters-report.md`.
-/

noncomputable section

open scoped Matrix

namespace CFSG.GorensteinWalter

universe u

/-! ## The rational parameter package -/

/-- Exactly the hypotheses of `secondCase_linearArithmetic`, packaged for
the downstream application. -/
public structure SecondCaseLinearParameters where
  q : ℚ
  k : ℚ
  k' : ℚ
  p : ℚ
  p0 : ℚ
  p1 : ℚ
  u : ℚ
  m : ℚ
  L : ℚ
  hq : 7 ≤ q
  hk : k ≤ (q + 1) / 2
  hk' : (q - 1) / 2 ≤ k'
  hp0 : 3 ≤ p0
  hp01 : p0 ≤ p1
  hp0p : p0 ≤ p
  hpk : 2 * p ≤ k
  hu : u ≤ p
  hu_nonneg : 0 ≤ u
  hL : L = (p1 - 1) * (q * k' - 1) - (q - 1) / p * q
  h10 : q * k' * m ≤ 6 * k ^ 2 * u ^ 3 * p0 ^ 3
  h11 : (p1 - 1) * q * k' * L ≤ m

/-! ## One-application theorem -/

/-- Any Section-4 linear parameter package feeds directly into the landed
arithmetic endpoint; this is the single application used by
`secondCase_linearContradictionData`. -/
public theorem secondCase_linearParameters_arithmetic
    (P : SecondCaseLinearParameters) :
    LinearCaseContradictionData := by
  exact @secondCase_linearArithmetic P.q P.k P.k' P.p P.p0 P.p1 P.u P.m P.L
    P.hq P.hk P.hk' P.hp0 P.hp01 P.hp0p P.hpk P.hu P.hu_nonneg P.hL P.h10
    P.h11

end CFSG.GorensteinWalter
