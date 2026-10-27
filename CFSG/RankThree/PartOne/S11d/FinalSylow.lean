module

public import CFSG.RankThree.PartOne.S11d.OutCentral

public section

namespace CFSG.RankThree.PartOne

open Subgroup
open scoped Pointwise
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type*} [Group G]

theorem two_le_of_conj_ne {p n : ℕ} (hp : p.Prime) {S : Subgroup G} (hS : IsCyclic S)
    (hcard : Nat.card S = p ^ n) {u : G} (hu : u ∈ normalizer (S : Set G)) (hup : u ^ p = 1)
    {y : G} (hy : y ∈ S) (hmove : u * y * u⁻¹ ≠ y) : 2 ≤ n := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨g, hg⟩ := hS.exists_generator
  set s0 : G := (g : G) with hs0
  have hmem : ∀ x ∈ S, ∃ m : ℤ, x = s0 ^ m := by
    intro x hx
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    refine ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    simpa [hs0] using this.symm
  have hord : orderOf s0 = p ^ n := by
    rw [hs0, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hs0S : s0 ∈ S := g.2
  interval_cases n
  ·
    have : s0 = 1 := orderOf_eq_one_iff.mp (by simpa using hord)
    obtain ⟨m, rfl⟩ := hmem y hy
    apply hmove
    rw [this]
    simp
  ·
    obtain ⟨k, hk⟩ := hmem _ ((mem_normalizer_iff.mp hu s0).mp hs0S)
    have hkp := pow_conj_eq_zpow hk p
    rw [hup, inv_one, mul_one, one_mul] at hkp
    have h1 : s0 ^ (k ^ p - 1) = 1 := by rw [zpow_sub, zpow_one, ← hkp, mul_inv_cancel]
    have h2 : (p : ℤ) ∣ k ^ p - 1 := by
      have := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rw [hord, pow_one] at this
      exact_mod_cast this
    have h3 : (p : ℤ) ∣ k - 1 := by
      have h1' : ((k ^ p - 1 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h2
      have h2' : ((k - 1 : ℤ) : ZMod p) = 0 := by
        push_cast at h1' ⊢
        rwa [ZMod.pow_card] at h1'
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h2'
    have h4 : s0 ^ (k - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hord, pow_one]
      exact_mod_cast h3
    have h5 : u * s0 * u⁻¹ = s0 := by
      rw [hk]
      rw [zpow_sub, zpow_one] at h4
      exact mul_inv_eq_one.mp h4
    obtain ⟨m, rfl⟩ := hmem y hy
    apply hmove
    rw [← conj_zpow, h5]

section Sylow

variable [Finite G]

theorem exists_sylow_of_transvection {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J A : Subgroup G}
    (hJ : CFSG.pRank p ↥J ≤ 1) (hAJ : A ≤ normalizer (J : Set G)) (hApg : IsPGroup p A) {y : G}
    (hyJ : y ∈ J) (hyp : ∃ k : ℕ, orderOf y = p ^ k) (hyA : y ∈ normalizer (A : Set G)) {u : G}
    (huA : u ∈ A) (hup : u ^ p = 1) (hmove : u * y * u⁻¹ ≠ y) :
    ∃ S : Subgroup G, IsSylowOf p S J ∧ IsCyclic S ∧ A ⊓ J ≤ S ∧ A ≤ normalizer (S : Set G) ∧
      zpowers y = S ∧ orderOf y = p ^ (Nat.card J).factorization p ∧
      2 ≤ (Nat.card J).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hzy : IsPGroup p (zpowers y) := isPGroup_zpowers_of_orderOf hyp
  have hKN : zpowers y ≤ normalizer (A : Set G) := zpowers_le.mpr hyA
  have hW : IsPGroup p (A ⊔ zpowers y : Subgroup G) := hApg.to_sup_of_normal_left' hzy hKN
  have hWJ : A ⊔ zpowers y ≤ normalizer (J : Set G) :=
    sup_le hAJ (zpowers_le.mpr (le_normalizer hyJ))
  obtain ⟨T, hT, hWT⟩ := exists_isSylowOf_ge (p := p) (K := J ⊔ (A ⊔ zpowers y))
    (Q := A ⊔ zpowers y) le_sup_right hW
  have hKJ : J ⊔ (A ⊔ zpowers y) ≤ normalizer (J : Set G) := sup_le le_normalizer hWJ
  have hS : IsSylowOf p (T ⊓ J) J := hT.inf_of_le_normalizer le_sup_left hKJ
  have hAT : A ≤ T := fun x hx => hWT (mem_sup_left hx)
  have hyT : y ∈ T := hWT (mem_sup_right (mem_zpowers y))
  have hAS : A ≤ normalizer ((T ⊓ J : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (hAT hx) (hAJ hx)
  have hScyc : IsCyclic (T ⊓ J : Subgroup G) :=
    isCyclic_of_pRank_le_one hp hp2 inf_le_right hS.isPGroup hJ
  have hyS : y ∈ T ⊓ J := ⟨hyT, hyJ⟩
  have hcard : Nat.card (T ⊓ J : Subgroup G) = p ^ (Nat.card J).factorization p := hS.card_eq
  have hgen : zpowers y = T ⊓ J :=
    zpowers_eq_of_conj_ne hp hp2 hScyc hS.isPGroup (hAS huA) hup hyS hmove
  refine ⟨T ⊓ J, hS, hScyc, le_inf (inf_le_left.trans hAT) inf_le_right, hAS, hgen, ?_,
    two_le_of_conj_ne hp hScyc hcard (hAS huA) hup hyS hmove⟩
  rw [← Nat.card_zpowers, hgen, hcard]

end Sylow

theorem mem_zpowers_pow_of_pow_eq_one {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) {y d : G}
    (hy : orderOf y = p ^ n) (hd : d ∈ zpowers y) (hdp : d ^ p = 1) : d ∈ zpowers (y ^ p) := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hd
  have h1 : y ^ (k * (p : ℤ)) = 1 := by
    rw [zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast] at *
    simpa [← zpow_natCast, ← zpow_mul] using hdp
  have h2 : (p : ℤ) ^ n ∣ k * (p : ℤ) := by
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rw [hy] at this
    exact_mod_cast this
  have h3 : (p : ℤ) ^ (n - 1) * p ∣ k * p := by
    have : (p : ℤ) ^ n = (p : ℤ) ^ (n - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    rwa [this] at h2
  have h4 : (p : ℤ) ^ (n - 1) ∣ k :=
    (mul_dvd_mul_iff_right (by exact_mod_cast hp.ne_zero)).mp h3
  have h5 : (p : ℤ) ∣ k := (dvd_pow_self (p : ℤ) (by omega)).trans h4
  obtain ⟨k', rfl⟩ := h5
  rw [zpow_mul, zpow_natCast]
  exact zpow_mem (mem_zpowers (y ^ p)) k'

theorem orderOf_pow_prime_of_eq {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) {y : G}
    (hy : orderOf y = p ^ n) : orderOf (y ^ p) = p ^ (n - 1) := by
  have h : p ∣ orderOf y := by
    rw [hy]
    exact dvd_pow_self p (by omega)
  rw [orderOf_pow_of_dvd hp.ne_zero h, hy]
  have : p ^ n = p ^ (n - 1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [this, Nat.mul_div_cancel _ hp.pos]

theorem exists_conj_zpowers_eq [Finite G] {p : ℕ} (hp : p.Prime) {H : Subgroup G}
    (hHcyc : ∀ P : Subgroup G, P ≤ H → IsPGroup p P → IsCyclic P) {ξ₁ ξ₂ : G} (h1 : ξ₁ ∈ H)
    (h2 : ξ₂ ∈ H) (hp1 : ∃ k : ℕ, orderOf ξ₁ = p ^ k) (hp2 : ∃ k : ℕ, orderOf ξ₂ = p ^ k)
    (hord : orderOf ξ₁ = orderOf ξ₂) : ∃ g ∈ H, zpowers (g * ξ₂ * g⁻¹) = zpowers ξ₁ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q₁, hQ₁, hξ₁⟩ := exists_isSylowOf_ge (p := p) (K := H) (Q := zpowers ξ₁)
    (zpowers_le.mpr h1) (isPGroup_zpowers_of_orderOf hp1)
  obtain ⟨Q₂, hQ₂, hξ₂⟩ := exists_isSylowOf_ge (p := p) (K := H) (Q := zpowers ξ₂)
    (zpowers_le.mpr h2) (isPGroup_zpowers_of_orderOf hp2)
  obtain ⟨k, hkH, hk⟩ := hQ₁.exists_mem_conj hQ₂
  refine ⟨k⁻¹, H.inv_mem hkH, ?_⟩
  have hξ₂' : k⁻¹ * ξ₂ * k ∈ Q₁ := (hk ξ₂).mp (hξ₂ (mem_zpowers ξ₂))
  have hcyc : IsCyclic Q₁ := hHcyc Q₁ hQ₁.le hQ₁.isPGroup
  have hle₂ : zpowers (k⁻¹ * ξ₂ * k) ≤ Q₁ := zpowers_le.mpr hξ₂'
  have hle₁ : zpowers ξ₁ ≤ Q₁ := hξ₁
  have hcard : Nat.card ((zpowers ξ₁).subgroupOf Q₁) =
      Nat.card ((zpowers (k⁻¹ * ξ₂ * k)).subgroupOf Q₁) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₁).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle₂).toEquiv, Nat.card_zpowers,
      Nat.card_zpowers, hord]
    exact (CFSG.RankThree.PGroups.orderOf_inv_mul_mul k ξ₂).symm
  have heq := (IsCyclic.subgroup_eq_iff_card_eq (G := Q₁)).mpr hcard
  have := (Subgroup.subgroupOf_inj).mp heq
  rw [inf_eq_left.mpr hle₁, inf_eq_left.mpr hle₂] at this
  simpa using this.symm

end CFSG.RankThree.PartOne
