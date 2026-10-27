module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Defs2

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open scoped commutatorElement

theorem P9a_three_not_dvd_two_pow (k : ℕ) : ¬ 3 ∣ 2 ^ k := by
  intro h
  have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  norm_num at h2

theorem P9a_eq_or_eq_inv_of_mem_zpowers {H : Type*} [Group H] {u y : H} (hu : u ^ 3 = 1)
    (hu1 : u ≠ 1) (hy : y ∈ Subgroup.zpowers u) (hy1 : y ≠ 1) : y = u ∨ y = u⁻¹ := by
  have hord : orderOf u = 3 := orderOf_eq_prime hu hu1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have hk : u ^ k = u ^ (k % 3) := by
    have h := zpow_mod_orderOf u k
    rw [hord] at h
    simpa using h.symm
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · exfalso
    apply hy1
    rw [hk, h, zpow_zero]
  · left
    rw [hk, h, zpow_one]
  · right
    rw [hk, h, zpow_two]
    exact eq_inv_of_mul_eq_one_right (by rw [← pow_three]; exact hu)

theorem P9a_pow_eq_or_eq_inv {H : Type*} [Group H] {u : H} (hu : u ^ 3 = 1) (hu1 : u ≠ 1)
    {k : ℕ} (hk : ¬ 3 ∣ k) : u ^ k = u ∨ u ^ k = u⁻¹ := by
  have hord : orderOf u = 3 := orderOf_eq_prime hu hu1
  have hk' : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rw [← pow_mod_orderOf, hord]
  rcases hk' with h | h
  · left
    rw [h, pow_one]
  · right
    rw [h, pow_two]
    exact eq_inv_of_mul_eq_one_right (by rw [← pow_three]; exact hu)

theorem P9a_exists_two_pow_lift {Kg : Type} [Group Kg] (N : Subgroup Kg) [N.Normal]
    (hN : IsPGroup 2 N) {w₀ : Kg} {n : ℕ} (hn : Nat.Coprime n 2)
    (hord : orderOf (QuotientGroup.mk w₀ : Kg ⧸ N) = n) :
    ∃ k : ℕ, orderOf (w₀ ^ 2 ^ k) = n ∧
      (QuotientGroup.mk (w₀ ^ 2 ^ k) : Kg ⧸ N) = (QuotientGroup.mk w₀ : Kg ⧸ N) ^ 2 ^ k := by
  have hmem : w₀ ^ n ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hord]
    exact pow_orderOf_eq_one _
  obtain ⟨k, hk⟩ := hN ⟨w₀ ^ n, hmem⟩
  have hk' : (w₀ ^ n) ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  refine ⟨k, ?_, QuotientGroup.mk_pow N w₀ (2 ^ k)⟩
  have hcop : Nat.Coprime (orderOf (QuotientGroup.mk w₀ : Kg ⧸ N)) (2 ^ k) := by
    rw [hord]
    exact Nat.Coprime.pow_right k hn
  have hqord : orderOf (QuotientGroup.mk (w₀ ^ 2 ^ k) : Kg ⧸ N) = n := by
    rw [QuotientGroup.mk_pow, Nat.Coprime.orderOf_pow hcop, hord]
  have hw1 : (w₀ ^ 2 ^ k) ^ n = 1 := by
    rw [pow_right_comm]
    exact hk'
  apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hw1)
  rw [← hqord]
  exact orderOf_map_dvd (QuotientGroup.mk' N) (w₀ ^ 2 ^ k)

theorem P9a_commutator_mem_iff {Kg : Type} [Group Kg] (N : Subgroup Kg) [N.Normal] (s a : Kg) :
    ⁅s, a⁆ ∈ N ↔ Commute (QuotientGroup.mk s : Kg ⧸ N) (QuotientGroup.mk a) := by
  rw [← QuotientGroup.eq_one_iff, ← commutatorElement_eq_one_iff_commute]
  have h := map_commutatorElement (QuotientGroup.mk' N : Kg →* Kg ⧸ N) s a
  simp only [QuotientGroup.mk'_apply] at h
  rw [h]

theorem P9a_exists_order9 {Kg : Type} [Group Kg] (N : Subgroup Kg) [N.Normal]
    (hN : IsPGroup 2 N) {a x w₀ : Kg} (hwb : orderOf (QuotientGroup.mk w₀ : Kg ⧸ N) = 9)
    (hcomm : Commute (QuotientGroup.mk a : Kg ⧸ N) (QuotientGroup.mk w₀))
    (hx : (QuotientGroup.mk x : Kg ⧸ N) ∈ Subgroup.zpowers ((QuotientGroup.mk w₀ : Kg ⧸ N) ^ 3))
    (hx1 : (QuotientGroup.mk x : Kg ⧸ N) ≠ 1) :
    ∃ s : Kg, orderOf s = 9 ∧ Commute (QuotientGroup.mk s : Kg ⧸ N) (QuotientGroup.mk a) ∧
      (QuotientGroup.mk s : Kg ⧸ N) ^ 3 = QuotientGroup.mk x := by
  obtain ⟨k, hk9, hkq⟩ := P9a_exists_two_pow_lift N hN (w₀ := w₀) (n := 9) (by norm_num) hwb
  have hu : ((QuotientGroup.mk w₀ : Kg ⧸ N) ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]
    have h := pow_orderOf_eq_one (QuotientGroup.mk w₀ : Kg ⧸ N)
    rw [hwb] at h
    exact h
  have hu1 : (QuotientGroup.mk w₀ : Kg ⧸ N) ^ 3 ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hwb] at h'
    norm_num at h'
  have hxA := P9a_eq_or_eq_inv_of_mem_zpowers hu hu1 hx hx1
  have hvC := P9a_pow_eq_or_eq_inv hu hu1 (P9a_three_not_dvd_two_pow k)
  have hv3 : ((QuotientGroup.mk w₀ : Kg ⧸ N) ^ 2 ^ k) ^ 3 =
      ((QuotientGroup.mk w₀ : Kg ⧸ N) ^ 3) ^ 2 ^ k := pow_right_comm _ _ _
  have hkey : (QuotientGroup.mk (w₀ ^ 2 ^ k) : Kg ⧸ N) ^ 3 = QuotientGroup.mk x ∨
      ((QuotientGroup.mk (w₀ ^ 2 ^ k) : Kg ⧸ N) ^ 3)⁻¹ = QuotientGroup.mk x := by
    rw [hkq, hv3]
    rcases hxA with h1 | h1 <;> rcases hvC with h2 | h2 <;> rw [h1, h2] <;> simp
  have hcw : Commute (QuotientGroup.mk a : Kg ⧸ N) (QuotientGroup.mk (w₀ ^ 2 ^ k)) := by
    rw [hkq]
    exact hcomm.pow_right _
  rcases hkey with hc | hc
  · exact ⟨w₀ ^ 2 ^ k, hk9, hcw.symm, hc⟩
  · refine ⟨(w₀ ^ 2 ^ k)⁻¹, by rw [orderOf_inv, hk9], ?_, ?_⟩
    · rw [QuotientGroup.mk_inv]
      exact hcw.symm.inv_left
    · rw [QuotientGroup.mk_inv, inv_pow, hc]

theorem leaf_P9a_of_P9K (hK : Leaf_P9K) :
    Leaf_P9L2 →
    ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
      A2Cfg G T M L D H K q → (9 : ℤ) ∣ (q : ℤ) - sgn4 q →
        ∃ w x : G, w ∈ K ∧ orderOf w = 9 ∧ w ∈ Subgroup.normalizer (a2R H : Set G) ∧
          x ∈ oTwoUpper H ∧ x ∈ K ∧ orderOf x = 3 ∧ w ^ 3 * x⁻¹ ∈ a2R H := by
  intro hL2 G _ _ T M L D H K q c h9q
  obtain ⟨a, x, haK, ha2, haO, hxY, hxK, hx3, hxa, hOR, hnorm⟩ := hK G T M L D H K q c
  have hcore : ∀ y : ↥K, (y : G) ∈ pCoreOf 2 K ↔ y ∈ CFSG.pCore 2 ↥K :=
    fun y => (Lem3328.mem_pCore_iff y).symm
  have hNP : IsPGroup 2 (CFSG.pCore 2 ↥K) := CFSG.pCore_isPGroup
  obtain ⟨a', rfl⟩ : ∃ a' : ↥K, (a' : G) = a := ⟨⟨a, haK⟩, rfl⟩
  obtain ⟨x', rfl⟩ : ∃ x' : ↥K, (x' : G) = x := ⟨⟨x, hxK⟩, rfl⟩
  have hA2 : (QuotientGroup.mk a' : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact (hcore _).1 (by rw [Subgroup.coe_pow]; exact ha2)
  have hA1 : (QuotientGroup.mk a' : ↥K ⧸ CFSG.pCore 2 ↥K) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact fun h => haO ((hcore a').2 h)
  have hā2 : orderOf (QuotientGroup.mk a' : ↥K ⧸ CFSG.pCore 2 ↥K) = 2 :=
    orderOf_eq_prime hA2 hA1
  have hx3' : x' ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hx3]
    exact pow_orderOf_eq_one _
  have hX3 : (QuotientGroup.mk x' : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hx3', QuotientGroup.mk_one]
  have hX1 : (QuotientGroup.mk x' : ↥K ⧸ CFSG.pCore 2 ↥K) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    intro h
    obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨↑x', (hcore x').2 h⟩
    have hj' : (↑x' : G) ^ 2 ^ j = 1 := by
      have h' := congrArg Subtype.val hj
      simpa using h'
    have hd : 3 ∣ 2 ^ j := by
      rw [← hx3]
      exact orderOf_dvd_of_pow_eq_one hj'
    exact P9a_three_not_dvd_two_pow j hd
  have hxb3 : orderOf (QuotientGroup.mk x' : ↥K ⧸ CFSG.pCore 2 ↥K) = 3 :=
    orderOf_eq_prime hX3 hX1
  have hcomm_x : Commute (QuotientGroup.mk a' : ↥K ⧸ CFSG.pCore 2 ↥K) (QuotientGroup.mk x') :=
    ((P9a_commutator_mem_iff _ x' a').1 ((hcore ⁅x', a'⁆).1 hxa)).symm
  obtain ⟨wb, hwb9, hwbc, hwbz⟩ := hL2 q c.q_prime c.q_mod h9q (↥K ⧸ CFSG.pCore 2 ↥K) c.model
    (QuotientGroup.mk a') hā2
  obtain ⟨w₀, rfl⟩ := QuotientGroup.mk_surjective wb
  have hcomm' : Commute (QuotientGroup.mk a' : ↥K ⧸ CFSG.pCore 2 ↥K) (QuotientGroup.mk w₀) := hwbc
  have hxz : (QuotientGroup.mk x' : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      Subgroup.zpowers ((QuotientGroup.mk w₀ : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 3) :=
    hwbz _ hxb3 hcomm_x.eq
  obtain ⟨s, hs9, hsc, hs3⟩ :=
    P9a_exists_order9 (CFSG.pCore 2 ↥K) hNP hwb9 hcomm' hxz hX1
  have hsK : ⁅s, a'⁆ ∈ CFSG.pCore 2 ↥K := (P9a_commutator_mem_iff _ s a').2 hsc
  have hsnorm : (s : G) ∈ Subgroup.normalizer (a2R H : Set G) :=
    hnorm (s : G) s.2 ((hcore ⁅s, a'⁆).2 hsK)
  have h3 : s ^ 3 * x'⁻¹ ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
      QuotientGroup.mk_inv, hs3, mul_inv_cancel]
  refine ⟨(s : G), (x' : G), s.2, ?_, hsnorm, hxY, hxK, hx3, ?_⟩
  · exact (Subgroup.orderOf_coe s).trans hs9
  · exact hOR ((hcore _).2 h3)

end CFSG.Quasithin.H13.NFa2
