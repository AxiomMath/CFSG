module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearParameters
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationNine
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Packaging the numerical Section-4 linear data

This module contains the purely interface-level constructor used by the
eventual PSL₂ branch integration.  All group-theoretic work is represented by
the already proved equation-(9) package and the two rational inequalities;
the constructor itself only transports the cardinal bounds to `ℚ` and derives
`q ≥ 7` and `2p ≤ k` from an odd prime divisor of `|K|`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public noncomputable def secondCase_linearParameters_of_equationData
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {w : SecondCaseWitness c}
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (D : SecondCaseLinearEquationNineData d K)
    {p p0 p1 u m L : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hpdvd : p ∣ Nat.card D.Kinv)
    (hp0 : 3 ≤ p0) (hp01 : p0 ≤ p1) (hp0p : p0 ≤ p)
    (hu : u ≤ p) (hu_nonneg : 0 ≤ u)
    (hL : (L : ℚ) = ((p1 : ℚ) - 1) *
      ((Nat.card K : ℚ) * (D.k' : ℚ) - 1) -
      ((Nat.card K : ℚ) - 1) / (p : ℚ) * (Nat.card K : ℚ))
    (h10 : (Nat.card K : ℚ) * (D.k' : ℚ) * (m : ℚ) ≤
      6 * (D.k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3)
    (h11 : ((p1 : ℚ) - 1) * (Nat.card K : ℚ) *
      (D.k' : ℚ) * (L : ℚ) ≤ (m : ℚ)) :
    SecondCaseLinearParameters := by
  have hqNat : 7 ≤ Nat.card K :=
    secondCase_equationNine_q_ge_seven_of_p_dvd_Kinv d K D hp hpodd hpdvd
  have hpkNat : 2 * p ≤ D.k :=
    secondCase_equationNine_two_p_le_k d K D hp hpodd hpdvd
  have hkRat : (D.k : ℚ) ≤ ((Nat.card K : ℚ) + 1) / 2 := D.hk_rat
  have hk'Rat : ((Nat.card K : ℚ) - 1) / 2 ≤ (D.k' : ℚ) := D.hk'_rat
  have hqRat : (7 : ℚ) ≤ (Nat.card K : ℚ) := by exact_mod_cast hqNat
  have hp0Rat : (3 : ℚ) ≤ (p0 : ℚ) := by exact_mod_cast hp0
  have hp01Rat : (p0 : ℚ) ≤ (p1 : ℚ) := by exact_mod_cast hp01
  have hp0pRat : (p0 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp0p
  have hpkRat : 2 * (p : ℚ) ≤ (D.k : ℚ) := by
    exact_mod_cast hpkNat
  have huRat : (u : ℚ) ≤ (p : ℚ) := by exact_mod_cast hu
  have huNonnegRat : (0 : ℚ) ≤ (u : ℚ) := by exact_mod_cast hu_nonneg
  exact
    { q := Nat.card K
      k := D.k
      k' := D.k'
      p := p
      p0 := p0
      p1 := p1
      u := u
      m := m
      L := L
      hq := hqRat
      hk := hkRat
      hk' := hk'Rat
      hp0 := hp0Rat
      hp01 := hp01Rat
      hp0p := hp0pRat
      hpk := hpkRat
      hu := huRat
      hu_nonneg := huNonnegRat
      hL := hL
      h10 := h10
      h11 := h11 }

end CFSG.GorensteinWalter
