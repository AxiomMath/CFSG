module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Fixed fields of odd prime-order coefficient automorphisms

This is the finite-field part of the odd semilinear centralizer route.  It
records the exact cardinality data needed by the later matrix calculation,
without making any claim about the centralizer itself.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A nontrivial odd prime-order field automorphism has a fixed subfield of
cardinality at least three, and the ambient field cardinality is the `p`th
power of that fixed-field cardinality. -/
public theorem finiteField_primeOrder_fixedSubfield_data
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (sigma : K ≃+* K) (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hord : orderOf sigma = p) :
    let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
    3 ≤ Nat.card R ∧ 3 ≤ p ∧ Nat.card K = Nat.card R ^ p := by
  let R := FixedPoints.subfield (Subgroup.zpowers sigma) K
  have hcardeq : Nat.card K = Nat.card R ^ orderOf sigma :=
    nat_card_eq_fixedSubfield_card_pow_orderOf K sigma
  have hcardpow : Nat.card K = Nat.card R ^ p := by
    simpa [hord] using hcardeq
  rcases hK with ⟨q, n, hq, hqodd, _hn, hKcard⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fintype K := Fintype.ofFinite K
  have hKcardF : Fintype.card K = q ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact hKcard
  let : CharP K q := charP_of_card_eq_prime_pow hKcardF
  let : Fintype R := Fintype.ofFinite R
  let : CharP R q := Subfield.charP R q
  have hRcard : ∃ m : ℕ+, Nat.Prime q ∧ Fintype.card R = q ^ (m : ℕ) :=
    FiniteField.card R q
  rcases hRcard with ⟨m, _hq', hRm⟩
  have hqge : 3 ≤ q := by
    have hq2 : 2 ≤ q := hq.two_le
    have hqne2 : q ≠ 2 := by
      intro h
      subst q
      exact hqodd.not_two_dvd_nat (by simp)
    omega
  have hRcard_ge : 3 ≤ Nat.card R := by
    rw [Nat.card_eq_fintype_card, hRm]
    calc
      3 ≤ q := hqge
      _ ≤ q ^ (m : ℕ) := Nat.le_pow m.pos
  have hpge : 3 ≤ p := by
    have hp2 : 2 ≤ p := hp.two_le
    have hpne2 : p ≠ 2 := by
      intro hp2eq
      have hdiv : 2 ∣ p := by simp [hp2eq]
      exact hpodd.not_two_dvd_nat hdiv
    omega
  exact ⟨hRcard_ge, hpge, hcardpow⟩

end CFSG.GorensteinWalter
