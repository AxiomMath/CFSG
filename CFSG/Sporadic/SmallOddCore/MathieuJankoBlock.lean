module

public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.ComponentInitial.IsotypicRepeatedPrimes
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.J1
public import CFSG.Sporadic.J3
public import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Sporadic.Schreier.M24Base

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

theorem ncard_prime_sq_dvd_le_two {N a b m : ℕ} (hN : N = 2 ^ a * 3 ^ b * m)
    (hm : ∀ r : ℕ, r.Prime → r ^ 2 ∣ m → False) :
    {r : ℕ | r.Prime ∧ r ^ 2 ∣ N}.ncard ≤ 2 := by
  have hsub : {r : ℕ | r.Prime ∧ r ^ 2 ∣ N} ⊆ {2, 3} := by
    rintro r ⟨hr, hrN⟩
    by_contra h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
    have hcop : Nat.Coprime (r ^ 2) (2 ^ a * 3 ^ b) := by
      refine Nat.Coprime.pow_left _ (Nat.Coprime.mul_right ?_ ?_)
      · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_two).mpr h.1)
      · exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hr Nat.prime_three).mpr h.2)
    rw [hN] at hrN
    exact hm r hr (hcop.dvd_of_dvd_mul_left hrN)
  calc {r : ℕ | r.Prime ∧ r ^ 2 ∣ N}.ncard ≤ ({2, 3} : Set ℕ).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 2 := Set.ncard_pair (by norm_num)

theorem not_prime_sq_dvd {m B : ℕ} (hm : 0 < m) (hB : m < (B + 1) ^ 2)
    (h : ∀ r ≤ B, 2 ≤ r → ¬ r ^ 2 ∣ m) : ∀ r : ℕ, r.Prime → r ^ 2 ∣ m → False := by
  intro r hr hrm
  have hle : r ^ 2 ≤ m := Nat.le_of_dvd hm hrm
  have hrB : r ≤ B := by
    by_contra hc
    have : (B + 1) ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  exact h r hrB hr.two_le hrm

variable {G : Type*} [Group G]

theorem nonempty_centerQuotient_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nonempty (A ⧸ center A ≃* B ⧸ center B) :=
  ⟨QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)⟩

theorem isQuasisimple_subgroupOf {J L : Subgroup G} (hq : CFSG.Assembly.IsQuasisimple J)
    (hJL : J ≤ L) : CFSG.Assembly.IsQuasisimple (J.subgroupOf L) := by
  rw [AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
  exact (isQuasisimple_congr (subgroupOfEquivOfLe hJL).symm).1 hq

theorem three_le_ncard_prime_sq_dvd [Finite G] {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hML : blockGroup J ≤ L) :
    3 ≤ {r : ℕ | r.Prime ∧ r ^ 2 ∣ Nat.card (L ⧸ center L)}.ncard := by
  obtain ⟨K, hK, hKJ⟩ := hΔ.exists_ne J
  have hJL : J ≤ L := (le_blockGroup mem_block_self).trans hML
  have hKL : K ≤ L := (le_blockGroup hK).trans hML
  obtain ⟨⟨g, hKg⟩, hcomm⟩ := hK
  have hJK : ⁅J, K⁆ = ⊥ := hcomm.resolve_left (Ne.symm hKJ)
  have hKq : CFSG.Assembly.IsQuasisimple K := isQuasisimple_of_isConjOf hq ⟨g, hKg⟩
  have hJK' : ⁅J.subgroupOf L, K.subgroupOf L⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    exact Subtype.ext (mem_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hJK (mem_subgroupOf.mp hx)) y.1
        (mem_subgroupOf.mp hy))
  let eJK : J ≃* K := (J.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hKg.symm)
  exact commuting_isotypic_quasisimple_factors_three_repeated_primes
    (isQuasisimple_subgroupOf hq hJL) (isQuasisimple_subgroupOf hKq hKL) hJK'
    (nonempty_centerQuotient_equiv (((subgroupOfEquivOfLe hJL).trans eJK).trans
      (subgroupOfEquivOfLe hKL).symm)) le_rfl

theorem not_nonempty_equiv_of_card [Finite G] {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hML : blockGroup J ≤ L) {X : Type*} [Group X] {a b m : ℕ}
    (hX : Nat.card X = 2 ^ a * 3 ^ b * m) (hm : ∀ r : ℕ, r.Prime → r ^ 2 ∣ m → False) :
    ¬ Nonempty (L ⧸ center L ≃* X) := by
  rintro ⟨e⟩
  have h3 := three_le_ncard_prime_sq_dvd hq hΔ hML
  have h2 := ncard_prime_sq_dvd_le_two ((Nat.card_congr e.toEquiv).trans hX) hm
  omega

theorem commuting_block_mathieu_j1_j3_overgroup_exclusion
    [Finite G] {J : Subgroup G}
    (hq : CFSG.Assembly.IsQuasisimple J) (_heven : Even (Nat.card J))
    (_hJ : IsUniversalComponent J) (hΔ : (block J).Nontrivial) {L : Subgroup G}
    (hML : blockGroup J ≤ L) :
    ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.M11) ∧
      ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.M12) ∧
      ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.M22) ∧
      ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.M23) ∧
      ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.M24) ∧
      ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.J1) ∧
      ¬ Nonempty (L ⧸ center L ≃* NativeSporadic.J3) := by
  have h55 := not_prime_sq_dvd (m := 55) (B := 7) (by norm_num) (by norm_num) (by decide)
  have h385 := not_prime_sq_dvd (m := 385) (B := 19) (by norm_num) (by norm_num) (by decide)
  have h8855 := not_prime_sq_dvd (m := 8855) (B := 94) (by norm_num) (by norm_num) (by decide)
  have h7315 := not_prime_sq_dvd (m := 7315) (B := 85) (by norm_num) (by norm_num) (by decide)
  have h1615 := not_prime_sq_dvd (m := 1615) (B := 40) (by norm_num) (by norm_num) (by decide)
  refine ⟨not_nonempty_equiv_of_card hq hΔ hML (X := NativeSporadic.M11) (a := 4) (b := 2)
      (CFSG.Sporadic.Schreier.m11_card.trans (by norm_num)) h55,
    not_nonempty_equiv_of_card hq hΔ hML (X := NativeSporadic.M12) (a := 6) (b := 3)
      (CFSG.Sporadic.Schreier.m12_card.trans (by norm_num)) h55,
    not_nonempty_equiv_of_card hq hΔ hML (X := NativeSporadic.M22) (a := 7) (b := 2)
      (CFSG.Sporadic.Schreier.m22_card.trans (by norm_num)) h385,
    not_nonempty_equiv_of_card hq hΔ hML (X := NativeSporadic.M23) (a := 7) (b := 2)
      (CFSG.Sporadic.Schreier.m23_card.trans (by norm_num)) h8855,
    not_nonempty_equiv_of_card hq hΔ hML (X := NativeSporadic.M24) (a := 10) (b := 3)
      (CFSG.Sporadic.Schreier.m24_card.trans (by norm_num)) h8855,
    not_nonempty_equiv_of_card hq hΔ hML (X := NativeSporadic.J1) (a := 3) (b := 1)
      (CFSG.Sporadic.J1.card_J1.trans (by norm_num)) h7315,
    not_nonempty_equiv_of_card hq hΔ hML (X := NativeSporadic.J3) (a := 7) (b := 5)
      (CFSG.Sporadic.J3.card_J3.trans (by norm_num)) h1615⟩

end CFSG.Sporadic.SmallOddCore
