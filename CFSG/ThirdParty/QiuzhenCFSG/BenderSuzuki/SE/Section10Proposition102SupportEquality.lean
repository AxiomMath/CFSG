module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102ExponentData
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section10Proposition102Hall

namespace CFSG
end CFSG
open CFSG

/-!
# Section 10, Proposition 10.2: exact prime-support bridge

The Hall assembly gives one implication from the derived subgroup's prime
support to the Peterfalvi kernel.  The reverse implication is the elementary
fixed/inverted cardinal factorization for the normalized odd derived subgroup.
This small helper packages the source phrase "have the same prime divisors"
without assuming any Proposition 10.2, Proposition 11.1, Theorem 6, or
Theorem SE conclusion.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- The derived subgroup and Peterfalvi anti-fixed set have the same prime
divisors once Hall support transfer is available. -/
public theorem proposition102_prime_support_iff_kset_card
    {X : Type u} [Group X] [Finite X]
    {D H : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDodd : Odd (Nat.card D))
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hHleD : H ≤ D)
    (hHnorm : t ∈ Subgroup.normalizer (H : Set X))
    (hKH : peterfalviKSet D t ⊆ H)
    (h42 : II1Lemma42PrimeTransfer (X := X))
    (hSupport : ∀ q : Nat.Primes, q ∈ subgroupPrimeSet H →
      q.val ∣ Nat.card (Subgroup.closure (peterfalviKSet D t))) :
    ∀ q : Nat.Primes,
      (q.val ∣ Nat.card H ↔
        q.val ∣ Nat.card {x : X // x ∈ peterfalviKSet D t}) := by
  intro q
  constructor
  · intro hqH
    have hqH' : q ∈ subgroupPrimeSet H := by
      simpa [subgroupPrimeSet] using hqH
    have hqK : q.val ∣ Nat.card
        (Subgroup.closure (peterfalviKSet D t)) := hSupport q hqH'
    exact h42 D t hDodd ht hDnorm q.val q.property hqK
  · intro hqI
    have hHodd : Odd (Nat.card H) := hDodd.of_dvd_nat
      (Subgroup.card_dvd_of_le hHleD)
    have hcard := theorem4b_card_eq_card_fixed_mul_inverted ht hHodd hHnorm
    have hInv : theorem4bInvertedCard t H =
        Nat.card {x : X // x ∈ peterfalviKSet D t} :=
      proposition102_invertedCard_eq_kset_card ht hHleD hKH
    have hdiv : Nat.card {x : X // x ∈ peterfalviKSet D t} ∣ Nat.card H := by
      rw [← hInv, hcard]
      exact dvd_mul_left _ _
    exact hqI.trans hdiv

end CFSG.BenderSuzuki
