module

public import CFSG.Permutation.FiveTransitive.HallBranchOrbitData
public import CFSG.Permutation.FiveTransitive.HallParityFromOriented
public import CFSG.Permutation.FiveTransitive.HallAmbientSylowStep

public section

namespace CFSG

namespace FiveTransitive.Research.HallSixContradiction

open MulAction
open Research.HallConfiguration
open Research.HallOrbitTransitivity
open Research.HallBranchOrbitData
open Research.HallAmbientSylowStep
open Research.HallReflectionFactories
open Research.HallParityFromOriented

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem false_of_sixPointConfiguration_card_ge_twentySeven
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (hX : 27 ≤ Fintype.card X)
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e)))
    (a b : G) (haTwo : a ^ 2 = 1) (hbTwo : b ^ 2 = 1)
    (hab : Commute a b)
    (haBase : ∀ i, a • e i =
      e (Research.SharpFourBound.baseSingleSwap i))
    (hbBase : ∀ i, b • e i =
      e (Research.SharpFourBound.baseDoubleSwap i))
    (p q : X) (hsix : SixPointConfiguration e a b p q) : False := by
  classical
  obtain ⟨y, hy, htLower, hcommon, _hconnect⟩ :=
    exists_regularOrbitData_six h4 hX e hodd a b haTwo hbTwo hab
      haBase hbBase p q hsix
  rcases hsix with ⟨hq, hpq, hFa, hFb, hFc, hEcard₀⟩
  have hap : a • p = q := hq.symm
  have hEcard : (exceptionalSet (X := X) a b).ncard = 6 := by
    simpa only [exceptionalSet, exceptionalFixedSet] using hEcard₀
  have he : ∀ i, e i ∈ exceptionalSet (X := X) a b := by
    intro i
    fin_cases i <;> simp [exceptionalSet, hFa, hFc]
  have hoddC : Odd (Nat.card (hallCentralizer (X := X) a b)) :=
    hallCentralizer_card_odd e a b he hodd
  let C := hallCentralizer (X := X) a b
  let t := (MulAction.orbit C y).ncard
  change 5 ≤ t at htLower
  change ∀ x : X, x ∉ exceptionalSet (X := X) a b →
    (MulAction.orbit C x).ncard = t at hcommon
  obtain ⟨ell, hellPrime, hellDvd⟩ :=
    Nat.exists_prime_and_dvd (show t ≠ 1 by omega)
  letI : Fact ell.Prime := ⟨hellPrime⟩
  have htDvdC : t ∣ Nat.card C := by
    have hindex := Subgroup.index_dvd_card (MulAction.stabilizer C y)
    rw [MulAction.index_stabilizer] at hindex
    exact hindex
  have hellC : ell ∣ Nat.card C := hellDvd.trans htDvdC
  have hellTwo : ell ≠ 2 := by
    intro hell
    subst ell
    exact hoddC.not_two_dvd_nat hellC
  obtain ⟨P, Q, hPQ, hfixedCases⟩ :=
    exists_ambientSylow_fixedPoints_cases e a b he (Or.inl hEcard)
      t hcommon hellDvd hellTwo
  have hfixed : MulAction.fixedPoints
      (Research.HallSylowNormalizer.ambientSylow e Q) X =
        exceptionalSet (X := X) a b := by
    rcases hfixedCases with hfixed | hexceptional
    · exact hfixed
    · omega
  obtain ⟨u, hu0, hu1, hu2, huq, hu3, hup⟩ :=
    exists_orientedQuarterTurn_six h4 e hodd a b haTwo hbTwo hab
      haBase hbBase p q hap hFa hFb hFc y hy
  exact false_of_six_fixedSet_and_oriented_quarterTurn
    h4 e hodd a b haTwo haBase hbBase p q hq hpq
      hFa hFb hFc hEcard Q hfixed u
      hu0 hu1 hu2 huq hu3 hup

end FiveTransitive.Research.HallSixContradiction

end CFSG
