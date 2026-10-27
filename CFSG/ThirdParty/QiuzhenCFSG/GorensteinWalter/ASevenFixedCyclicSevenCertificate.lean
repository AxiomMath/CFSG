module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

namespace CFSG.GorensteinWalter

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
public theorem a7_fixed_cyclic_seven_certificate :
    ∀ x : ASevenCertificateGroup,
      (x ≠ 1 ∧ x ^ 7 = 1 ∧
        fixedSpanPow 7 x (a7t * x * a7t⁻¹)) →
      a7t * x = x * a7t := by
  unfold fixedSpanPow
  intro x hx
  rcases hx with ⟨hxne, hxpow, i, hi⟩
  let : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hxorder : orderOf x = 7 := orderOf_eq_prime hxpow hxne
  have ht2 : a7t ^ 2 = 1 := by decide
  have htwice : x = (x ^ (i : Nat)) ^ (i : Nat) := by
    calc
      x = a7t ^ 2 * x * (a7t ^ 2)⁻¹ := by rw [ht2]; simp
      _ = a7t * (a7t * x * a7t⁻¹) * a7t⁻¹ := by
        simp only [pow_two]
        group
      _ = a7t * x ^ (i : Nat) * a7t⁻¹ := by rw [hi]
      _ = (a7t * x * a7t⁻¹) ^ (i : Nat) := by
        simpa using (map_pow (MulAut.conj a7t) x (i : Nat))
      _ = (x ^ (i : Nat)) ^ (i : Nat) := by rw [hi]
  have hmod : 1 ≡ (i : Nat) * (i : Nat) [MOD 7] := by
    have h := (pow_eq_pow_iff_modEq
      (x := x) (n := 1) (m := (i : Nat) * (i : Nat))).mp (by
        simpa [pow_mul] using htwice)
    simpa [hxorder] using h
  have hiCases : (i : Nat) = 1 ∨ (i : Nat) = 6 := by
    have hiLt : (i : Nat) < 7 := i.isLt
    interval_cases hival : (i : Nat) <;>
      norm_num [Nat.ModEq, hival] at hmod <;> omega
  rcases hiCases with hi1 | hi6
  · have hconj : a7t * x * a7t⁻¹ = x := by simpa [hi1] using hi
    calc
      a7t * x = (a7t * x * a7t⁻¹) * a7t := by group
      _ = x * a7t := by rw [hconj]
  · exfalso
    let sigma : Equiv.Perm (Fin 7) := x
    have hsigmaOrder : orderOf sigma = 7 := by
      simpa [sigma, Subgroup.orderOf_coe] using hxorder
    have hcycle : sigma.IsCycle :=
      Equiv.Perm.isCycle_of_prime_order'' Nat.prime_seven (by
        simpa using hsigmaOrder)
    have hsupp : sigma.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [← hcycle.orderOf, hsigmaOrder]
      simp
    have h4move : sigma (4 : Fin 7) ≠ 4 := by
      rw [← Equiv.Perm.mem_support, hsupp]
      simp
    have h5move : sigma (5 : Fin 7) ≠ 5 := by
      rw [← Equiv.Perm.mem_support, hsupp]
      simp
    obtain ⟨k, hk⟩ := hcycle.exists_pow_eq h4move h5move
    have ht4 : (a7t : Equiv.Perm (Fin 7)) 4 = 4 := by decide
    have ht5 : (a7t : Equiv.Perm (Fin 7)) 5 = 5 := by decide
    have htInv4 : (a7t : Equiv.Perm (Fin 7))⁻¹ 4 = 4 := by decide
    have hconjPow : a7t * x ^ k * a7t⁻¹ = x ^ (6 * k) := by
      calc
        a7t * x ^ k * a7t⁻¹ = (a7t * x * a7t⁻¹) ^ k := by
          simpa using (map_pow (MulAut.conj a7t) x k)
        _ = (x ^ 6) ^ k := by simpa [hi6] using congrArg (fun z => z ^ k) hi
        _ = x ^ (6 * k) := by rw [pow_mul]
    have hk6 : (sigma ^ (6 * k)) 4 = 5 := by
      have happly := congrArg (fun z : ASevenCertificateGroup =>
        (z : Equiv.Perm (Fin 7)) 4) hconjPow
      simpa [sigma, Equiv.Perm.mul_apply, htInv4, ht5, hk] using happly.symm
    have hpows : sigma ^ k = sigma ^ (6 * k) :=
      hcycle.pow_eq_pow_iff.mpr ⟨4, h4move, hk.trans hk6.symm⟩
    have hkmod : k ≡ 6 * k [MOD 7] := by
      rw [← hsigmaOrder, ← pow_eq_pow_iff_modEq]
      exact hpows
    have hdivInt : (7 : ℤ) ∣ (5 : ℤ) * k := by
      convert hkmod.dvd using 1 <;> push_cast <;> ring
    have hdivNat : 7 ∣ 5 * k := by exact_mod_cast hdivInt
    have h7dvd : 7 ∣ k := by
      rcases Nat.prime_seven.dvd_mul.mp hdivNat with hbad | hk'
      · norm_num at hbad
      · exact hk'
    have hsigmaK : sigma ^ k = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hsigmaOrder]
      exact h7dvd
    have hfalse : (4 : Fin 7) = 5 := by simpa [hsigmaK] using hk
    exact (by decide : (4 : Fin 7) ≠ 5) hfalse

end CFSG.GorensteinWalter
