module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Centralization of invariant odd-prime subgroups in S4

An odd-prime subgroup of `S₄` normalized by the centralizer of an
involution is centralized by that involution.  Order considerations reduce
to a subgroup of order three; the remaining finite fact is certified over
the concrete permutation group.
-/

namespace CFSG.GorensteinWalter

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 2000000 in
/-- If an odd-prime subgroup of `S₄` is invariant under the centralizer of
an involution, then that involution centralizes the subgroup. -/
public theorem sFour_invariant_oddP_subgroup_centralized
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup (Equiv.Perm (Fin 4))) (hPp : IsPGroup p P)
    {t : Equiv.Perm (Fin 4)} (ht : IsInvolution t)
    (hPinv : Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 4))) ≤
      Subgroup.normalizer (P : Set (Equiv.Perm (Fin 4)))) :
    P ≤ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 4))) := by
  have hcert : ∀ (a s : Equiv.Perm (Fin 4)),
      (a ≠ 1 ∧ a ^ 3 = 1) → (s ≠ 1 ∧ s ^ 2 = 1) →
      (∀ c : Equiv.Perm (Fin 4), c * s = s * c →
        c * a * c⁻¹ = a ∨ c * a * c⁻¹ = a ^ 2) →
      a * s = s * a := by
    decide
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hGcard : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
  have hPdvd : Fintype.card P ∣ 24 := by
    have h := Subgroup.card_subgroup_dvd_card P
    simpa [hGcard] using h
  rcases hPp.exists_card_eq with ⟨n, hn⟩
  rw [Nat.card_eq_fintype_card] at hn
  by_cases hnzero : n = 0
  · have hPcard : Nat.card P = 1 := by
      rw [Nat.card_eq_fintype_card, hn, hnzero]
      simp
    have hPbot : P = ⊥ := Subgroup.eq_bot_of_card_eq P hPcard
    intro x hx
    have hxone : x = 1 := by
      rw [hPbot] at hx
      exact Subgroup.mem_bot.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff, hxone]
    simp
  · have hpdvd : p ∣ 24 := by
      apply (show p ∣ Fintype.card P from ?_).trans hPdvd
      rw [hn]
      exact dvd_pow_self p hnzero
    have hpeq : p = 3 := by
      have hfactor : 24 = 2 ^ 3 * 3 := by norm_num
      rw [hfactor] at hpdvd
      rcases hp.dvd_mul.mp hpdvd with htwo | hthree
      · have hp2 : p = 2 :=
          Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two htwo
        subst p
        exact False.elim (hpodd.not_two_dvd_nat (by norm_num))
      · exact ((Nat.dvd_prime Nat.prime_three).mp hthree).resolve_left hp.ne_one
    subst p
    have hnle : n ≤ 1 := by
      by_contra hnnot
      have htwo : 2 ≤ n := by omega
      have hbad : 9 ∣ 24 := by
        apply (pow_dvd_pow 3 htwo).trans
        simpa [hn] using hPdvd
      norm_num at hbad
    have hnone : n = 1 := by omega
    have hPcard : Fintype.card P = 3 := by simpa [hnone] using hn
    have hPcardNat : Nat.card P = 3 := by
      rw [Nat.card_eq_fintype_card, hPcard]
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨xP, hxPorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := P) 3 (by rw [hPcardNat])
    let x : Equiv.Perm (Fin 4) := xP
    have hxorder : orderOf x = 3 := by
      simpa [x, Subgroup.orderOf_coe] using hxPorder
    have hxne : x ≠ 1 := by
      intro hxone
      have : (3 : ℕ) = 1 := by rw [← hxorder, hxone, orderOf_one]
      norm_num at this
    have hxpow : x ^ 3 = 1 := by
      rw [← hxorder]
      exact pow_orderOf_eq_one x
    have hZle : Subgroup.zpowers x ≤ P :=
      Subgroup.zpowers_le.mpr xP.property
    have hZcard : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, hxorder]
    have hZeq : Subgroup.zpowers x = P := by
      apply Subgroup.eq_of_le_of_card_ge hZle
      rw [hZcard, hPcardNat]
    have hnorm : ∀ c : Equiv.Perm (Fin 4), c * t = t * c →
        c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x ^ 2 := by
      intro c hc
      have hcCent : c ∈
          Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 4))) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hc
      have hcNorm := hPinv hcCent
      have hconjP : c * x * c⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hcNorm x).mp xP.property
      rw [← hZeq] at hconjP
      rcases Subgroup.mem_zpowers_iff.mp hconjP with ⟨k, hk⟩
      have hnonneg : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg _ (by norm_num)
      have hlt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
      rw [zpow_eq_zpow_emod' k hxpow] at hk
      interval_cases hrem : k % (3 : ℤ)
      · simp at hk
        exfalso
        apply hxne
        calc
          x = c⁻¹ * (c * x * c⁻¹) * c := by group
          _ = 1 := by rw [← hk]; simp
      · simp at hk
        exact Or.inl hk.symm
      · right
        rw [← zpow_natCast]
        exact hk.symm
    have hxt : x * t = t * x :=
      hcert x t ⟨hxne, hxpow⟩ (by simpa only [IsInvolution] using ht) hnorm
    rw [← hZeq]
    exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_centralizer_singleton_iff.mpr hxt)

end CFSG.GorensteinWalter
