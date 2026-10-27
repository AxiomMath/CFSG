module

public import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.RankThree.PartOne.D4RC

open Subgroup
open scoped commutatorElement

theorem rcb_conj_eq_self_of_pow_mem_centralizer {K : Type*} [Group K] {p : ℕ} [hp : Fact p.Prime]
    {A : Subgroup K} (hA : IsPGroup p A) (hAc : IsCyclic A) {g : K}
    (hg : g ∈ normalizer (A : Set K)) {n : ℕ} (hn : ¬ p ∣ n)
    (hgn : g ^ n ∈ centralizer (A : Set K)) (hΩ : ∀ a ∈ A, a ^ p = 1 → g * a * g⁻¹ = a) :
    ∀ a ∈ A, g * a * g⁻¹ = a := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_generator (α := A)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA c
  have hord : orderOf (c : K) = p ^ k := by rw [Subgroup.orderOf_coe, hk]
  have hgen : ∀ x ∈ A, ∃ m : ℤ, (c : K) ^ m = x := fun x hx => by
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hc ⟨x, hx⟩)
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  obtain ⟨u, hu⟩ := hgen _ ((mem_normalizer_iff.mp hg (c : K)).mp c.2)
  have hpow : ∀ j : ℕ, g ^ j * (c : K) * (g ^ j)⁻¹ = (c : K) ^ (u ^ j) := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      have : g ^ (j + 1) * (c : K) * (g ^ (j + 1))⁻¹ =
          g * (g ^ j * (c : K) * (g ^ j)⁻¹) * g⁻¹ := by simp [pow_succ', mul_assoc]
      rw [this, ih, ← conj_zpow, ← hu, ← zpow_mul, pow_succ']
  have hdvd : ∀ z : ℤ, (c : K) ^ z = 1 → (p : ℤ) ^ k ∣ z := fun z hz => by
    have := orderOf_dvd_iff_zpow_eq_one.mpr hz
    rwa [hord, Nat.cast_pow] at this
  have h1 : (p : ℤ) ^ k ∣ u ^ n - 1 := by
    apply hdvd
    have h2 : (c : K) * g ^ n = g ^ n * (c : K) := mem_centralizer_iff.mp hgn _ c.2
    have h3 : g ^ n * (c : K) * (g ^ n)⁻¹ = c := mul_inv_eq_iff_eq_mul.mpr h2.symm
    rw [hpow] at h3
    rw [zpow_sub_one, h3, mul_inv_cancel]
  have h4 : (p : ℤ) ^ k ∣ u - 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    have hbA : (c : K) ^ (p ^ (k - 1)) ∈ A := A.pow_mem c.2 _
    have hbp : ((c : K) ^ (p ^ (k - 1))) ^ p = 1 := by
      rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hk0, ← hord, pow_orderOf_eq_one]
    have h5 := hΩ _ hbA hbp
    have h6 : (c : K) ^ ((u - 1) * (p : ℤ) ^ (k - 1)) = 1 := by
      have h7 : g * (c : K) ^ (p ^ (k - 1)) * g⁻¹ = ((c : K) ^ u) ^ (p ^ (k - 1)) := by
        rw [hu, ← conj_pow]
      rw [h7] at h5
      have h8 : (c : K) ^ (u * ((p ^ (k - 1) : ℕ) : ℤ)) = (c : K) ^ ((p ^ (k - 1) : ℕ) : ℤ) := by
        rw [zpow_mul, zpow_natCast, zpow_natCast, h5]
      rw [sub_mul, one_mul, zpow_sub]
      push_cast at h8
      rw [h8, mul_inv_cancel]
    have h8 := hdvd _ h6
    have h9 : (p : ℤ) ∣ u - 1 := by
      have : (p : ℤ) * (p : ℤ) ^ (k - 1) ∣ (u - 1) * (p : ℤ) ^ (k - 1) := by
        rwa [← pow_succ', Nat.sub_add_cancel hk0]
      exact (mul_dvd_mul_iff_right (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))).mp this
    have hx : ¬ (p : ℤ) ∣ u := fun h => by
      have : (p : ℤ) ∣ 1 := by simpa using dvd_sub h h9
      exact hp.out.not_dvd_one (by exact_mod_cast this)
    have hn' : ¬ (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hn
    have := emultiplicity_pow_sub_pow_of_prime (Nat.prime_iff_prime_int.mp hp.out) h9 hx hn'
    rw [one_pow] at this
    rw [pow_dvd_iff_le_emultiplicity] at h1 ⊢
    rwa [this] at h1
  have h10 : (c : K) ^ (u - 1) = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rwa [hord, Nat.cast_pow]
  have h11 : g * (c : K) * g⁻¹ = c := by
    rw [← hu]
    rw [zpow_sub_one, mul_inv_eq_one] at h10
    exact h10
  intro a ha
  obtain ⟨m, rfl⟩ := hgen a ha
  rw [← conj_zpow, h11]

theorem rcb_exists_pow_mem_centralizer {K : Type*} [Group K] {A : Subgroup K}
    (hAC : A ≤ centralizer (A : Set K)) {g : K} (hg : g ∈ normalizer (A : Set K)) :
    ∃ n : ℕ, n ∣ A.index ∧ g ^ n ∈ centralizer (A : Set K) := by
  refine ⟨(centralizer (A : Set K)).relIndex (normalizer (A : Set K)),
    (relIndex_dvd_of_le_left _ hAC).trans (relIndex_dvd_index_of_le le_normalizer), ?_⟩
  have h1 := pow_index_mem A.normalizerMonoidHom.ker (⟨g, hg⟩ : normalizer (A : Set K))
  rw [normalizerMonoidHom_ker] at h1
  exact h1

theorem rcb_exists_normalizer_elt_perfect {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) {A : Subgroup K} (hA : IsPGroup p A)
    (hAidx : ¬ p ∣ A.index) (hAc : IsCyclic A) (hA1 : A ≠ ⊥) :
    ∃ g ∈ normalizer (A : Set K), ∃ a ∈ A, a ^ p = 1 ∧ g * a * g⁻¹ ≠ a := by
  by_contra hcon
  have hΩ : ∀ g ∈ normalizer (A : Set K), ∀ a ∈ A, a ^ p = 1 → g * a * g⁻¹ = a :=
    fun g hg a ha hap => by_contra fun h => hcon ⟨g, hg, a, ha, hap, h⟩
  have hAC : A ≤ centralizer (A : Set K) := fun a ha => mem_centralizer_iff.mpr fun b hb =>
    congrArg Subtype.val (mul_comm' (⟨b, hb⟩ : A) ⟨a, ha⟩)
  have hNC : normalizer (A : Set K) ≤ centralizer (A : Set K) := fun g hg => by
    obtain ⟨n, hn, hgn⟩ := rcb_exists_pow_mem_centralizer hAC hg
    have := rcb_conj_eq_self_of_pow_mem_centralizer hA hAc hg (fun h => hAidx (h.trans hn)) hgn
      (hΩ g hg)
    exact mem_centralizer_iff.mpr fun a ha => (mul_inv_eq_iff_eq_mul.mp (this a ha)).symm
  let S : Sylow p K := hA.toSylow hAidx
  have hNC' : normalizer (S : Set K) ≤ centralizer (S : Set K) := hNC
  have : IsMulCommutative (S : Subgroup K) :=
    ⟨⟨fun a b => Subtype.ext (hNC' (le_normalizer b.2) a a.2)⟩⟩
  let f : K →* (S : Subgroup K) := MonoidHom.transferSylow S hNC'
  have hker : (⊤ : Subgroup K) ≤ f.ker := by
    rw [← hperf]
    exact Abelianization.commutator_subset_ker f
  have hdisj := MonoidHom.ker_transferSylow_disjoint S hNC' A hA
  rw [top_le_iff.mp hker] at hdisj
  exact hA1 (top_disjoint.mp hdisj)

set_option linter.unusedVariables false in
theorem rcb_exists_normalizer_elt {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {P A : Subgroup G} (hperf : ⁅P, P⁆ = P) (hAP : A ≤ P) (hA : IsPGroup p A)
    (hAidx : ¬ p ∣ A.relIndex P) (hAc : IsCyclic A) (hA1 : A ≠ ⊥) :
    ∃ g ∈ P, g ∈ Subgroup.normalizer (A : Set G) ∧ ∃ a ∈ A, a ^ p = 1 ∧ g * a * g⁻¹ ≠ a := by
  have hA'p : IsPGroup p (A.subgroupOf P) := hA.of_equiv (subgroupOfEquivOfLe hAP).symm
  have hA'c : IsCyclic (A.subgroupOf P) := (subgroupOfEquivOfLe hAP).symm.isCyclic.mp hAc
  have hA'1 : A.subgroupOf P ≠ ⊥ := fun h => hA1 ((subgroupOf_eq_bot.mp h).eq_bot_of_le hAP)
  have hperf' : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = ⊤ := by
    apply Subgroup.map_injective (f := P.subtype) (Subgroup.subtype_injective P)
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hperf]
  obtain ⟨g, hg, a, ha, hap, hne⟩ := rcb_exists_normalizer_elt_perfect hperf' hA'p hAidx hA'c hA'1
  refine ⟨g, g.2, ?_, a, ha, congrArg Subtype.val hap, fun h => hne (Subtype.ext h)⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact (mem_normalizer_iff.mp hg ⟨h, hAP hh⟩).mp hh
  · intro hh
    have hhP : h ∈ P := by
      have := P.mul_mem (P.mul_mem (P.inv_mem g.2) (hAP hh)) g.2
      simpa [mul_assoc] using this
    exact (mem_normalizer_iff.mp hg ⟨h, hhP⟩).mpr hh

end CFSG.RankThree.PartOne.D4RC
