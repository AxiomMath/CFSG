module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModI

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem orderOf_conj' (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := MulEquiv.orderOf_eq (MulAut.conj g) x
  simpa [MulAut.conj_apply] using this

theorem normalizer_le_normalizer_oTwoUpper (K : Subgroup G) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (oTwoUpper K : Set G) := by
  intro g hg
  apply normalizer_of_maps
  intro w hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    exact Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hx.1,
      by rw [orderOf_conj']; exact hx.2⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have := (oTwoUpper K).mul_mem hx hy
    simpa [mul_assoc] using this
  | inv x _ hx =>
    have := (oTwoUpper K).inv_mem hx
    simpa [mul_assoc] using this

omit [Finite G] in
theorem oTwoUpper_le_of_pow {H N : Subgroup G} (hpow : ∀ h ∈ H, ∃ k : ℕ, h ^ (2 ^ k) ∈ N) :
    oTwoUpper H ≤ N := by
  rw [oTwoUpper, Subgroup.closure_le]
  rintro x ⟨hxH, hodd⟩
  obtain ⟨k, hk⟩ := hpow x hxH
  obtain ⟨e, he⟩ := exists_pow_eq_self_of_coprime
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd))
  rw [← he]
  exact N.pow_mem hk e

omit [Finite G] in
theorem pow_mul_mem {N : Subgroup G} {c : G} (hc : c ∈ Subgroup.normalizer (N : Set G))
    {n : G} (hn : n ∈ N) : ∀ m : ℕ, (n * c) ^ m * (c ^ m)⁻¹ ∈ N
  | 0 => by simp
  | m + 1 => by
    have ih := pow_mul_mem hc hn m
    have e : (n * c) ^ (m + 1) * (c ^ (m + 1))⁻¹ =
        ((n * c) ^ m * (c ^ m)⁻¹) * (c ^ m * n * (c ^ m)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    refine N.mul_mem ih ?_
    have hcm : c ^ m ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ hc m
    exact (Subgroup.mem_normalizer_iff.1 hcm n).1 hn

omit [Finite G] in
theorem pow_mem_of_mul {N K : Subgroup G} (hK : IsPGroup 2 K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) {n c : G} (hn : n ∈ N) (hc : c ∈ K) :
    ∃ k : ℕ, (n * c) ^ (2 ^ k) ∈ N := by
  obtain ⟨k, hk⟩ := hK ⟨c, hc⟩
  have hk' : c ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  refine ⟨k, ?_⟩
  have := pow_mul_mem (hKN hc) hn (2 ^ k)
  rwa [hk', inv_one, mul_one] at this

section Idx3

variable {I N : Subgroup G}

omit [Finite G] in
theorem not_mem_of_orderOf_three (hN2 : IsPGroup 2 N) {y : G} (hy : orderOf y = 3) : y ∉ N := by
  intro hyN
  obtain ⟨k, hk⟩ := hN2 ⟨y, hyN⟩
  have hk' : y ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h3 := orderOf_dvd_of_pow_eq_one hk'
  rw [hy] at h3
  have := (Nat.prime_dvd_prime_iff_eq (Nat.prime_three) Nat.prime_two).1
    (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

omit [Finite G] in
theorem card_quot_three (h3 : N.relIndex I = 3) :
    Nat.card (↥I ⧸ N.subgroupOf I) = 3 := by
  rw [← Subgroup.index, ← Subgroup.relIndex]
  exact h3

variable [hNn : (N.subgroupOf I).Normal]

omit [Finite G] in
theorem quot_ne_one (hN2 : IsPGroup 2 N) {y : G} (hyI : y ∈ I) (hy : orderOf y = 3) :
    (QuotientGroup.mk ⟨y, hyI⟩ : ↥I ⧸ N.subgroupOf I) ≠ 1 := by
  rw [Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact not_mem_of_orderOf_three hN2 hy

theorem quot_pow (h3 : N.relIndex I = 3) {a b : ↥I ⧸ N.subgroupOf I} (ha : a ≠ 1) :
    ∃ k < 3, a ^ k = b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb := mem_zpowers_of_prime_card (card_quot_three h3) ha (g' := b)
  rw [← mem_powers_iff_mem_zpowers] at hb
  obtain ⟨n, rfl⟩ := hb
  have ho : orderOf a = 3 := orderOf_eq_prime (by
    rw [← card_quot_three h3]
    exact pow_card_eq_one') ha
  refine ⟨n % 3, Nat.mod_lt _ (by norm_num), ?_⟩
  rw [← ho, pow_mod_orderOf]

theorem idx3_exists (h3 : N.relIndex I = 3) : ∃ y ∈ I, orderOf y = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := ↥I ⧸ N.subgroupOf I) 3
    (by rw [card_quot_three h3])
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hx0 : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
  have hdvd : 3 ∣ orderOf x := by
    rw [← hq]
    exact orderOf_map_dvd (QuotientGroup.mk' _) x
  rw [← Subgroup.orderOf_coe] at hx0 hdvd
  exact ⟨((x : G)) ^ (orderOf (x : G) / 3), I.pow_mem x.2 _, orderOf_pow_orderOf_div hx0 hdvd⟩

theorem idx3_pair (hN2 : IsPGroup 2 N) (h3 : N.relIndex I = 3) {y y' : G} (hy : y ∈ I)
    (hy' : y' ∈ I) (o : orderOf y = 3) (o' : orderOf y' = 3) : y * y'⁻¹ ∈ N ∨ y * y' ∈ N := by
  obtain ⟨k, hk, he⟩ := quot_pow h3 (b := (QuotientGroup.mk ⟨y', hy'⟩ : ↥I ⧸ N.subgroupOf I))
    (quot_ne_one hN2 hy o)
  interval_cases k
  · exact absurd he.symm (by rw [pow_zero]; exact quot_ne_one hN2 hy' o')
  · left
    have e : (QuotientGroup.mk (⟨y, hy⟩ * (⟨y', hy'⟩ : ↥I)⁻¹) : ↥I ⧸ N.subgroupOf I) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← he, pow_one, mul_inv_cancel]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at e
    exact e
  · right
    have e : (QuotientGroup.mk (⟨y, hy⟩ * (⟨y', hy'⟩ : ↥I)) : ↥I ⧸ N.subgroupOf I) = 1 := by
      have ho : orderOf (QuotientGroup.mk ⟨y, hy⟩ : ↥I ⧸ N.subgroupOf I) = 3 :=
        orderOf_eq_prime (by rw [← card_quot_three h3]; exact pow_card_eq_one')
          (quot_ne_one hN2 hy o)
      rw [QuotientGroup.mk_mul, ← he, ← pow_succ', show 2 + 1 = 3 from rfl, ← ho,
        pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at e
    exact e

theorem idx3_coset (hN2 : IsPGroup 2 N) (h3 : N.relIndex I = 3) {y : G} (hy : y ∈ I)
    (o : orderOf y = 3) {i : G} (hi : i ∈ I) : ∃ k : ℕ, i * (y ^ k)⁻¹ ∈ N := by
  obtain ⟨k, -, he⟩ := quot_pow h3 (b := (QuotientGroup.mk ⟨i, hi⟩ : ↥I ⧸ N.subgroupOf I))
    (quot_ne_one hN2 hy o)
  refine ⟨k, ?_⟩
  have e : (QuotientGroup.mk (⟨i, hi⟩ * ((⟨y, hy⟩ : ↥I) ^ k)⁻¹) : ↥I ⧸ N.subgroupOf I) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow, he, mul_inv_cancel]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at e
  simpa using e

end Idx3

end CFSG.Quasithin.H13.S127.Mod

end
