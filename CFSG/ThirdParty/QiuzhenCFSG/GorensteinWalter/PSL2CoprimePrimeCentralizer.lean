module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

open BenderSuzuki.MatrixGroups

universe u

/-- In `PSL₂(F)`, an element of the defining-characteristic prime order does
not commute with an element of a distinct prime order.  The proof uses the
II.8.5(a) partition: the product of two commuting elements of distinct prime
orders would have order divisible by both primes, while each partition piece
has either defining-characteristic order or torus order prime to the defining
characteristic. -/
public theorem psl2_no_commuting_distinct_prime_order
    {F : Type u} [Field F] [Finite F]
    {r f p : ℕ} [Fact r.Prime] [Fact p.Prime]
    (hFcard : Nat.card F = r ^ f) (hpne : p ≠ r)
    {a b : PSL2MatrixGroup F}
    (haorder : orderOf a = r) (hborder : orderOf b = p)
    (hcomm : Commute a b) : False := by
  classical
  obtain ⟨U, S, hUcyc, hUcard, hScyc, hScard, hpart⟩ :=
    BenderSuzuki.External.huppert_II_8_5_a_psl2_partition
      (F := F) (p := r) (f := f) hFcard
      (default : Sylow r (PSL2MatrixGroup F))
  let z : PSL2MatrixGroup F := a * b
  have hcop : Nat.Coprime (orderOf a) (orderOf b) := by
    rw [haorder, hborder]
    exact (Fact.out : Nat.Prime r).coprime_iff_not_dvd.mpr (by
      intro h
      rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp h with h1 | heq
      · exact (Fact.out : Nat.Prime r).ne_one h1
      · exact hpne heq.symm)
  have hzorder : orderOf z = r * p := by
    simpa [z, haorder, hborder] using
      hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
  have hzne : z ≠ 1 := by
    intro hz
    have hzorderone : orderOf z = 1 := orderOf_eq_one_iff.mpr hz
    rw [hzorder] at hzorderone
    have hprod : r * p = 1 := hzorderone
    have hlt : 1 < r * p := one_lt_mul
      (Fact.out : Nat.Prime r).one_le (Fact.out : Nat.Prime p).one_lt
    exact (Nat.ne_of_gt hlt) hprod
  obtain ⟨T, hzTmem, _hTuniq⟩ := hpart z hzne
  rcases hzTmem with ⟨hzT, hfamily⟩
  rcases hfamily with hroot | hsplit | hnonsplit
  · rcases hroot with ⟨g, hg⟩
    have hTcard : Nat.card T = Nat.card F := by
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      obtain ⟨eP⟩ :=
        BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
          hFcard (default : Sylow r (PSL2MatrixGroup F))
      exact (Nat.card_congr eP.toEquiv).symm
    have hdiv : r * p ∣ Nat.card F := by
      have hdivT : orderOf z ∣ Nat.card T := by
        have h0 := orderOf_dvd_natCard (⟨z, hzT⟩ : T)
        have ho : orderOf (⟨z, hzT⟩ : T) = orderOf z := by
          exact (Subgroup.orderOf_coe (⟨z, hzT⟩ : T)).symm
        rw [ho] at h0
        exact h0
      rw [hzorder, hTcard] at hdivT
      exact hdivT
    have hpdiv : p ∣ r ^ f := by
      have hpdivF : p ∣ Nat.card F :=
        dvd_trans (by simpa [Nat.mul_comm] using (dvd_mul_right p r)) hdiv
      rw [hFcard] at hpdivF
      exact hpdivF
    have hpr : p ∣ r := (Fact.out : Nat.Prime p).dvd_of_dvd_pow hpdiv
    rcases (Nat.dvd_prime (Fact.out : Nat.Prime r)).mp hpr with hone | heq
    · exact (Fact.out : Nat.Prime p).ne_one hone
    · exact hpne heq
  · rcases hsplit with ⟨g, hg⟩
    have hTcard : Nat.card T = (Nat.card F - 1) /
        Nat.gcd (Nat.card F - 1) 2 := by
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hUcard
    have hdivT : orderOf z ∣ Nat.card T := by
      have h0 := orderOf_dvd_natCard (⟨z, hzT⟩ : T)
      have ho : orderOf (⟨z, hzT⟩ : T) = orderOf z := by
        exact (Subgroup.orderOf_coe (⟨z, hzT⟩ : T)).symm
      rw [ho] at h0
      exact h0
    have hdiv : r ∣ Nat.card F - 1 := by
      have hrord : r ∣ orderOf z := by
        rw [hzorder]
        exact dvd_mul_right r p
      have hd : r ∣ (Nat.card F - 1) /
          Nat.gcd (Nat.card F - 1) 2 := by
        rw [← hTcard]
        exact dvd_trans hrord hdivT
      exact dvd_trans hd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
    have hrF : r ∣ Nat.card F := by
      rw [hFcard]
      exact dvd_pow_self r
        (Glauberman.Dickson.huppert_II_8_27_field_exponent_ne_zero hFcard)
    have hrone : r ∣ 1 := by
      have hdiff := Nat.dvd_sub hrF hdiv
      have hqpos : 1 ≤ Nat.card F := by
        have := Nat.card_pos (α := F)
        omega
      have hEq : Nat.card F - (Nat.card F - 1) = 1 := by omega
      rw [hEq] at hdiff
      exact hdiff
    exact (Fact.out : Nat.Prime r).not_dvd_one hrone
  · rcases hnonsplit with ⟨g, hg⟩
    have hTcard : Nat.card T = (Nat.card F + 1) /
        Nat.gcd (Nat.card F - 1) 2 := by
      rw [hg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hScard
    have hdivT : orderOf z ∣ Nat.card T := by
      have h0 := orderOf_dvd_natCard (⟨z, hzT⟩ : T)
      have ho : orderOf (⟨z, hzT⟩ : T) = orderOf z := by
        exact (Subgroup.orderOf_coe (⟨z, hzT⟩ : T)).symm
      rw [ho] at h0
      exact h0
    have hdiv : r ∣ Nat.card F + 1 := by
      have hrord : r ∣ orderOf z := by
        rw [hzorder]
        exact dvd_mul_right r p
      have hd : r ∣ (Nat.card F + 1) /
          Nat.gcd (Nat.card F - 1) 2 := by
        rw [← hTcard]
        exact dvd_trans hrord hdivT
      have hgcd : Nat.gcd (Nat.card F - 1) 2 ∣ Nat.card F + 1 := by
        have hsum := Nat.dvd_add (Nat.gcd_dvd_left (Nat.card F - 1) 2)
          (Nat.gcd_dvd_right (Nat.card F - 1) 2)
        have hqpos : 1 ≤ Nat.card F := by
          have := Nat.card_pos (α := F)
          omega
        have hEq : Nat.card F - 1 + 2 = Nat.card F + 1 := by omega
        rw [hEq] at hsum
        exact hsum
      exact dvd_trans hd (Nat.div_dvd_of_dvd hgcd)
    have hrF : r ∣ Nat.card F := by
      rw [hFcard]
      exact dvd_pow_self r
        (Glauberman.Dickson.huppert_II_8_27_field_exponent_ne_zero hFcard)
    have hrone : r ∣ 1 := by
      have hdiff := Nat.dvd_sub hdiv hrF
      have hqpos : 1 ≤ Nat.card F := by
        have := Nat.card_pos (α := F)
        omega
      have hEq : Nat.card F + 1 - Nat.card F = 1 := by omega
      rw [hEq] at hdiff
      exact hdiff
    exact (Fact.out : Nat.Prime r).not_dvd_one hrone

end CFSG.GorensteinWalter
