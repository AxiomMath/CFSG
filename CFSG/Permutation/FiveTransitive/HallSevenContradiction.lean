module

public import CFSG.Permutation.FiveTransitive.HallBranchOrbitData
public import CFSG.Permutation.FiveTransitive.HallParityFromOriented
public import CFSG.Permutation.FiveTransitive.HallExceptionalOrbitArithmetic
public import CFSG.Permutation.FiveTransitive.HallThreeOrbitExtraction
public import CFSG.Permutation.FiveTransitive.HallAmbientSylowStep

public section

namespace CFSG

namespace FiveTransitive.Research.HallSevenContradiction

open MulAction
open Research.HallConfiguration
open Research.HallOrbitTransitivity
open Research.HallBranchOrbitData
open Research.HallAmbientSylowStep
open Research.HallReflectionFactories
open Research.HallParityFromOriented
open Research.HallRegularOrbits
open Research.HallSylowFromC
open Research.HallSylowNormalizer
open Research.HallExceptionalOrbitArithmetic
open Research.HallThreeOrbitExtraction
open Research.HallExceptionalContradiction

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem false_of_sevenPointConfiguration_card_ge_twentySeven
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
    (p q : X) (hseven : SevenPointConfiguration e a b p q) : False := by
  classical
  obtain ⟨r, y, hpq, hpr, hqr, hFa, hFb, hFc, hD,
      hSet, hBT, hTcard, hy, htLower, hcommon, _hconnect⟩ :=
    exists_regularOrbitData_seven h4 hX e hodd a b haTwo hbTwo hab
      haBase hbBase p q hseven
  have hq : q = a • p := hseven.1
  have hap : a • p = q := hq.symm
  have hEcard : (exceptionalSet (X := X) a b).ncard = 7 := by
    rw [hSet, Set.ncard_union_eq hBT,
      Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin, hTcard]
  have he : ∀ i, e i ∈ exceptionalSet (X := X) a b := by
    intro i
    rw [hSet]
    exact Or.inl ⟨i, rfl⟩
  have hoddC : Odd (Nat.card (hallCentralizer (X := X) a b)) :=
    hallCentralizer_card_odd e a b he hodd
  obtain ⟨u, hu0, hu1, hur, hu2, huq, hu3, hup⟩ :=
    exists_orientedQuarterTurn_seven h4 e hodd a b haTwo hbTwo hab
      haBase hbBase p q r hap hFa hFb hD y hy
  let C := hallCentralizer (X := X) a b
  let t := (MulAction.orbit C y).ncard
  change 5 ≤ t at htLower
  change ∀ x : X, x ∉ exceptionalSet (X := X) a b →
    (MulAction.orbit C x).ncard = t at hcommon
  have htDvdC : t ∣ Nat.card C := by
    have hindex := Subgroup.index_dvd_card (MulAction.stabilizer C y)
    rw [MulAction.index_stabilizer] at hindex
    exact hindex
  rcases exists_prime_ne_three_dvd_or_eq_three_pow t (by omega) with
      hprime | hthreePow
  · obtain ⟨ell, hellPrime, hellDvd, hellNeThree⟩ := hprime
    letI : Fact ell.Prime := ⟨hellPrime⟩
    have hellC : ell ∣ Nat.card C := hellDvd.trans htDvdC
    have hellTwo : ell ≠ 2 := by
      intro hell
      subst ell
      exact hoddC.not_two_dvd_nat hellC
    obtain ⟨P, Q, hPQ, hfixedCases⟩ :=
      exists_ambientSylow_fixedPoints_cases e a b he (Or.inr hEcard)
        t hcommon hellDvd hellTwo
    rcases hfixedCases with hfixed | hexceptional
    · exact false_of_seven_fixedSet_and_oriented_quarterTurn
        h4 e hodd a b haTwo haBase hbBase p q r hq hpq
          hFa hFb hFc hD hEcard Q hfixed u
          hu0 hu1 hur hu2 huq hu3 hup
    · exact (hellNeThree hexceptional.1).elim
  · obtain ⟨w, hwpos, htPow⟩ := hthreePow
    have hwTwo : 2 ≤ w := by
      by_contra hwTwo
      have hwOne : w = 1 := by omega
      rw [hwOne, pow_one] at htPow
      omega
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hthreeDvd : 3 ∣ t := by
      rw [htPow]
      exact dvd_pow_self 3 (by omega)
    obtain ⟨P, Q, hPQ, hfixedCases⟩ :=
      exists_ambientSylow_fixedPoints_cases e a b he (Or.inr hEcard)
        t hcommon hthreeDvd (by norm_num)
    rcases hfixedCases with hfixed | hexceptional
    · exact false_of_seven_fixedSet_and_oriented_quarterTurn
        h4 e hodd a b haTwo haBase hbBase p q r hq hpq
          hFa hFb hFc hD hEcard Q hfixed u
          hu0 hu1 hur hu2 huq hu3 hup
    · let A : Subgroup G := ambientSylow e Q
      let P₀ : Subgroup G := sylowImage C P
      have hfixedRange : MulAction.fixedPoints A X = Set.range e := by
        simpa only [A] using hexceptional.2.2
      have hA : IsPGroup 3 A := by
        exact Q.isPGroup'.map (MulAction.stabilizer G e).subtype
      have hCfix : ∀ c : C, ∀ x ∈ exceptionalSet (X := X) a b,
          (c : G) • x = x := by
        intro c x hx
        exact (mem_hallCentralizer_iff a b (c : G)).mp c.prop |>.1 x hx
      have hPfix : exceptionalSet (X := X) a b ⊆
          MulAction.fixedPoints P₀ X := by
        exact exceptional_subset_fixedPoints_sylowImage
          C P (exceptionalSet (X := X) a b) hCfix
      have hP₀OrbitCard : ∀ x : X,
          x ∉ exceptionalSet (X := X) a b →
          (MulAction.orbit P₀ x).ncard = t := by
        intro x hx
        have hPorbit : MulAction.orbit P x = MulAction.orbit C x :=
          sylow_orbit_eq_of_orbit_ncard_eq_prime_pow P x (by
            rw [hcommon x hx, htPow])
        change (MulAction.orbit (sylowImage C P) x).ncard = t
        rw [orbit_sylowImage_eq C P x, hPorbit, hcommon x hx]
      have horbitTriple : MulAction.orbit A p = ({p, q, r} : Set X) :=
        pgroup_orbit_eq_triple A P₀ hA (by simpa only [A, P₀] using hPQ)
          (Set.range e) ({p, q, r} : Set X)
          (exceptionalSet (X := X) a b) hfixedRange hSet hBT hTcard
          p (by simp) hPfix t w htPow hwTwo hP₀OrbitCard
      have hbase : ∀ z : A, ∀ i, (z : G) • e i = e i := by
        intro z i
        have hz := ambientSylow_le_stabilizer e Q z.prop
        rw [MulAction.mem_stabilizer_iff] at hz
        have hi := congrArg (fun f : Fin 4 ↪ X ↦ f i) hz
        simpa [Function.Embedding.smul_apply, Subgroup.smul_def] using hi
      obtain ⟨z, hzbase, hzp, hzq, hzr⟩ :=
        exists_oriented_threeCycle_of_isPGroup_orbit
          A hA e hbase p q r hpq hpr hqr horbitTriple
      have hq0 : q ≠ e 0 := by
        intro h
        exact Set.disjoint_left.mp hBT ⟨0, h.symm⟩ (by simp)
      have hq1 : q ≠ e 1 := by
        intro h
        exact Set.disjoint_left.mp hBT ⟨1, h.symm⟩ (by simp)
      have hq3 : q ≠ e 3 := by
        intro h
        exact Set.disjoint_left.mp hBT ⟨3, h.symm⟩ (by simp)
      have he2p : e 2 ≠ p := by
        intro h
        exact Set.disjoint_left.mp hBT ⟨2, rfl⟩ (by rw [h]; simp)
      exact false_of_oriented_threeCycle_and_quarterTurn
        h4 e hodd p q r hq0 hq1 hq3 he2p z u
          (hzbase 0) (hzbase 1) (hzbase 2) (hzbase 3)
          hzp hzq hzr hu0 hu1 hur hu2 huq hu3 hup

end FiveTransitive.Research.HallSevenContradiction

end CFSG
