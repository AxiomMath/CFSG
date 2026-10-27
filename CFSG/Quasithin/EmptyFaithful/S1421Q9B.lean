module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.RankThree.PartOne.KLC.PRankTwo
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.RankThree.PartOne.KLC

namespace Q9

variable {G : Type} [Group G]

theorem two_le_pRank_of_commute_mod_two_group [Finite G] {X R : Subgroup G} (hR : IsPGroup 2 R)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) {a b : G} (ha : a ∈ X) (hb : b ∈ X)
    (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hcomm : a * b * a⁻¹ * b⁻¹ ∈ R)
    (hind : ∀ i j : ℤ, a ^ i * b ^ j ∈ R → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j) :
    2 ≤ CFSG.Open.pRank 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup ↥X := R.subgroupOf X with hN
  have : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hXR
  have hN2 : IsPGroup 2 N := IsPGroup.comap_subtype hR
  have hN3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨n, hn⟩ := hN2.exists_card_eq
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  let a' : ↥X ⧸ N := QuotientGroup.mk ⟨a, ha⟩
  let b' : ↥X ⧸ N := QuotientGroup.mk ⟨b, hb⟩
  have hc : Commute a' b' := by
    show a' * b' = b' * a'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hN,
      Subgroup.mem_subgroupOf]
    have hba : (b * a)⁻¹ ∈ X := X.inv_mem (X.mul_mem hb ha)
    have h1 := (Subgroup.mem_normalizer_iff.mp (hXR hba) (a * b * a⁻¹ * b⁻¹)⁻¹).mp
      (R.inv_mem hcomm)
    have h2 : (b * a)⁻¹ * (a * b * a⁻¹ * b⁻¹)⁻¹ * (b * a)⁻¹⁻¹ = (a * b)⁻¹ * (b * a) := by
      group
    rw [h2] at h1
    exact h1
  have h1 : a' ^ 3 = 1 := by
    show (QuotientGroup.mk ⟨a, ha⟩ : ↥X ⧸ N) ^ 3 = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨a, ha⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
    rw [this]
    rfl
  have h2 : b' ^ 3 = 1 := by
    show (QuotientGroup.mk ⟨b, hb⟩ : ↥X ⧸ N) ^ 3 = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨b, hb⟩ : ↥X) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this]
    rfl
  have hi : ∀ i j : ℤ, a' ^ i * b' ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j := by
    intro i j hij
    apply hind i j
    have h3 : (QuotientGroup.mk ((⟨a, ha⟩ : ↥X) ^ i * (⟨b, hb⟩ : ↥X) ^ j) : ↥X ⧸ N) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow, QuotientGroup.mk_zpow]
      exact hij
    rw [QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at h3
    simpa using h3
  have h4 := two_le_pRank_of_two_commuting Nat.prime_three hc h1 h2 hi
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_quotient_eq N hN3,
    ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h4
  exact h4

theorem exists_orderOf_three_of_isAlt_five [Finite G] {K : Subgroup G} (h : IsAlt 5 (ModO2 K)) :
    ∃ a ∈ K, orderOf a = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := h
  have h60 : Nat.card (ModO2 K) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  have hdvd : Nat.card (ModO2 K) ∣ Nat.card K := by
    have := Subgroup.index_mul_card (CFSG.pCore 2 ↥K)
    exact ⟨Nat.card (CFSG.pCore 2 ↥K), this.symm⟩
  have h3 : 3 ∣ Nat.card K := by
    refine dvd_trans ?_ hdvd
    rw [h60]
    norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 h3
  exact ⟨x, x.2, by rw [← hx]; exact Subgroup.orderOf_coe x⟩

end Q9

end CFSG.Quasithin
