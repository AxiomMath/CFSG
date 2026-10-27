module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GWLemma21Trichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

namespace CFSG
end CFSG
open CFSG

/-!
# Involution fusion in odd projective special linear groups

This extracts the model-side fusion input used in the component branch of
Gorenstein--Walter Theorem 2.6.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- All involutions of `PSL₂(K)` are conjugate when `K` has odd
prime-power order. -/
public theorem psl2_involutions_conjugate_of_odd_prime_power
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    ∀ x y : PSL2 K, IsInvolution x → IsInvolution y →
      ∃ g : PSL2 K, g * x * g⁻¹ = y := by
  classical
  have hcard_ge : 3 ≤ Nat.card K := by
    rcases hK with ⟨p, n, hp, hpodd, hn, hcard⟩
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      exact hpodd.not_two_dvd_nat (by simp)
    have hpge : 3 ≤ p := by
      have hp2 := hp.two_le
      omega
    rw [hcard]
    exact hpge.trans (by
      calc
        p = p ^ 1 := by simp
        _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn)
  by_cases hcard3 : Nat.card K = 3
  · let : Fintype K := Fintype.ofFinite K
    have hFcard : Fintype.card K = 3 := by
      simpa [Nat.card_eq_fintype_card] using hcard3
    let eK : ZMod 3 ≃+* K :=
      ZMod.ringEquivOfPrime K Nat.prime_three hFcard
    let e : PSL2 K ≃* alternatingGroup (Fin 4) :=
      (psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup
    have hA4 : ∀ a b : alternatingGroup (Fin 4),
        IsInvolution a → IsInvolution b →
          ∃ g : alternatingGroup (Fin 4), g * a * g⁻¹ = b := by
      intro a b
      revert a b
      simp only [IsInvolution]
      decide
    intro x y hx hy
    have hex : IsInvolution (e x) := by
      constructor
      · intro h
        exact hx.1 (e.injective (by simpa using h))
      · simpa using congrArg e hx.2
    have hey : IsInvolution (e y) := by
      constructor
      · intro h
        exact hy.1 (e.injective (by simpa using h))
      · simpa using congrArg e hy.2
    obtain ⟨g, hg⟩ := hA4 (e x) (e y) hex hey
    refine ⟨e.symm g, ?_⟩
    apply e.injective
    simpa using hg
  · have hcard_gt : 3 < Nat.card K := by omega
    have hSimple : IsSimpleGroup (PSL2 K) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    have hno2 : ¬ ∃ N : Subgroup (PSL2 K), N.Normal ∧ N.index = 2 := by
      rintro ⟨N, hNnormal, hNindex⟩
      rcases (haveI := hNnormal; hSimple.eq_bot_or_eq_top_of_normal N) with hNbot | hNtop
      · let S : Sylow 2 (PSL2 K) := Classical.choice Sylow.nonempty
        obtain ⟨m, hm, ⟨eS⟩⟩ :=
          psl2_odd_hasDihedralSylowTwo_model K hK S
        have hcardQge : 4 ≤ Nat.card (PSL2 K) := by
          have hcardS : Nat.card (S : Subgroup (PSL2 K)) = 2 * 2 ^ m := by
            exact (Nat.card_congr eS.toEquiv).trans DihedralGroup.nat_card
          have hfour : 4 ≤ Nat.card (S : Subgroup (PSL2 K)) := by
            rw [hcardS]
            have hpow : 2 ≤ 2 ^ m := by
              calc
                2 = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
            omega
          exact hfour.trans
            (Nat.le_of_dvd Nat.card_pos S.card_subgroup_dvd_card)
        have hcardQ : Nat.card (PSL2 K) = 2 := by
          rw [hNbot, Subgroup.index_bot] at hNindex
          exact hNindex
        omega
      · rw [hNtop, Subgroup.index_top] at hNindex
        omega
    have hnormal4to2 :
        (∃ N : Subgroup (PSL2 K), N.Normal ∧ N.index = 4) →
          ∃ N : Subgroup (PSL2 K), N.Normal ∧ N.index = 2 := by
      rintro ⟨N4, hN4, hindex4⟩
      let : N4.Normal := hN4
      let : Fintype ((PSL2 K) ⧸ N4) := N4.fintypeQuotientOfFiniteIndex
      have hcardQ : Nat.card ((PSL2 K) ⧸ N4) = 4 := by
        rw [← N4.index_eq_card, hindex4]
      have h2dvd : 2 ∣ Fintype.card ((PSL2 K) ⧸ N4) := by
        rw [← Nat.card_eq_fintype_card, hcardQ]
        norm_num
      obtain ⟨x, hx2⟩ :=
        exists_prime_orderOf_dvd_card (G := (PSL2 K) ⧸ N4) 2 h2dvd
      let J : Subgroup ((PSL2 K) ⧸ N4) := Subgroup.zpowers x
      have hJcard : Nat.card J = 2 := by
        rw [Nat.card_zpowers, hx2]
      have hJindex : J.index = 2 := by
        have hprod := J.index_mul_card
        rw [hJcard, hcardQ] at hprod
        exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
          (by simpa [mul_comm] using hprod)
      have hJnormal : J.Normal := Subgroup.normal_of_index_eq_two hJindex
      let N : Subgroup (PSL2 K) := J.comap (QuotientGroup.mk' N4)
      have hNnormal : N.Normal := hJnormal.comap (QuotientGroup.mk' N4)
      have hNindex : N.index = 2 := by
        rw [Subgroup.index_comap_of_surjective J
          (QuotientGroup.mk'_surjective N4)]
        exact hJindex
      exact ⟨N, hNnormal, hNindex⟩
    rcases gw_lemma_2_1
        (psl2_odd_hasDihedralSylowTwo_model K hK) with hfirst | hrest
    · exact hfirst.2.1
    · rcases hrest with hsecond | hthird
      · exact False.elim (hno2 hsecond.1)
      · exact False.elim (hno2 (hnormal4to2 hthird.1))

end CFSG.GorensteinWalter
