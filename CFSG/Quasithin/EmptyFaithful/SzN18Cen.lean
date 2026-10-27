module

public import CFSG.Quasithin.EmptyFaithful.S153LList3
public import CFSG.Quasithin.EmptyFaithful.R3c2Types
public import CFSG.Quasithin.EmptyFaithful.A38c4Main
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Cases

public section

namespace CFSG.Quasithin.SzN18

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

private theorem map_mem_center {A B : Type*} [Group A] [Group B] (e : A ≃* B) {a : A}
    (ha : a ∈ Subgroup.center A) : e a ∈ Subgroup.center B := by
  rw [Subgroup.mem_center_iff] at ha ⊢
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← map_mul, ← map_mul, ha x]

private theorem pow_three_of_center_eq_bot {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := by
  intro z hz
  have h1 : e z ∈ Subgroup.center Y := map_mem_center e hz
  rw [h, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h1
  rw [h1, one_pow]

private theorem pow_three_of_sl {n : ℕ} {K : Type} [Field K] {X : Type} [Group X]
    (e : X ≃* ↥(StatedSL n K)) (hr : ∀ r : K, r ^ n = 1 → r ^ 3 = 1) :
    ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := by
  intro z hz
  set φ := specialLinearGroupEquivStatedSL n K with hφ
  have hA : φ.symm (e z) ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) :=
    map_mem_center (φ.symm) (map_mem_center e hz)
  obtain ⟨r, hrn, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hrn
  have hA3 : (φ.symm (e z)) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrA, ← map_pow, hr r hrn, map_one]
    rfl
  have h3 : e (z ^ 3) = 1 := by
    have := congrArg φ hA3
    rw [map_pow, MulEquiv.apply_symm_apply, map_one] at this
    rw [map_pow]
    exact this
  exact e.injective (by rw [h3, map_one])

private theorem eq_one_of_sq_eq_one {K : Type} [Field K] [CharP K 2] {r : K} (h : r ^ 2 = 1) :
    r = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h0 : (r - 1) ^ 2 = 0 := by linear_combination h + (1 - r) * h2
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)

private theorem charP_two {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])

theorem center_pow_three_of_list
    {X : Type} [Group X] [Finite X] (hl : B56QuasisimpleList X) (hq : CFSG.IsQuasisimple X) :
    ∀ z ∈ Subgroup.center X, z ^ 3 = 1 := by
  rcases hl with ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨n, K, _, _, hK, ⟨e⟩⟩ |
    ⟨n, K, _, _, hK, ⟨e⟩⟩ | he6 | he7 | hhat | ⟨K, _, _, hK, ⟨e⟩⟩ | he4 | he5
  ·
    have := charP_two hK
    exact pow_three_of_sl e fun r hr => by
      have hr1 : r = 1 := eq_one_of_sq_eq_one (by simpa using hr)
      rw [hr1, one_pow]
  ·
    exact pow_three_of_sl e fun r hr => hr
  ·
    have hn : 2 ≤ n := by
      by_contra hn
      have h1 := R3c2.one_le_of_natCard_eq_two_pow hK
      obtain rfl : n = 1 := by omega
      exact R3c2.not_isQuasisimple_statedSp_two (by simpa using hK) e hq
    exact pow_three_of_center_eq_bot e (factA318Excl_holds.1 K n hn hK).1
  ·
    have hn : 2 ≤ n := by
      by_contra hn
      have h1 := R3c2.one_le_of_natCard_eq_two_pow hK
      obtain rfl : n = 1 := by omega
      exact R3c2.not_isQuasisimple_quasithinG2_two (by simpa using hK) e hq
    have hcard : 2 < Nat.card K := by
      rw [hK]
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    obtain ⟨c, hc0, hc1⟩ := CFSG.Quasithin.Vol2.KGNat.exists_ne_zero_ne_one (K := K) hcard
    have := charP_two hK
    have hZ : Subgroup.center ↥(CFSG.Open.quasithinG2 K) = ⊥ := by
      rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
      exact A318Excl.center_cayleyGroup_eq_bot hc0 hc1
    exact pow_three_of_center_eq_bot e hZ
  ·
    obtain ⟨e⟩ := he6
    exact pow_three_of_center_eq_bot e (alternatingGroup.center_eq_bot (by simp [Nat.card_eq_fintype_card]))
  ·
    obtain ⟨e⟩ := he7
    exact pow_three_of_center_eq_bot e (alternatingGroup.center_eq_bot (by simp [Nat.card_eq_fintype_card]))
  ·
    intro z hz
    have h3 : Nat.card (Subgroup.center X) = 3 := hhat.2.1
    have h := pow_card_eq_one' (G := ↥(Subgroup.center X)) (x := (⟨z, hz⟩ : ↥(Subgroup.center X)))
    rw [h3] at h
    simpa using congrArg Subtype.val h
  ·
    have hs : IsSimpleGroup ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ :=
      H13.isSimpleGroup_g2Two_commutator hK
    have : IsSimpleGroup ↥⁅CFSG.Open.quasithinG2 K, CFSG.Open.quasithinG2 K⁆ := hs
    have : IsSimpleGroup X := e.isSimpleGroup
    obtain ⟨-, -, a, b, hab⟩ := hq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have hZ : Subgroup.center X = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
      · exact h
      · exfalso
        apply hab
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)]
    intro z hz
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, one_pow]
  ·
    obtain ⟨e⟩ := he4
    exact pow_three_of_sl e (by decide)
  ·
    obtain ⟨e⟩ := he5
    exact pow_three_of_sl e (by decide)

theorem normal_eq_bot_of_coprime_three
    {X : Type} [Group X] [Finite X] (hl : B56QuasisimpleList X) (hq : CFSG.IsQuasisimple X)
    (N : Subgroup X) [N.Normal] (hN : ∀ n ∈ N, Nat.Coprime (orderOf n) 3) : N = ⊥ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (N := N) inferInstance with htop | hcen
  · exfalso
    have h3 : 3 ∣ Nat.card X := S153L.three_dvd_card_of_b56QL hl hq
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
    have h1 := hN x (htop ▸ Subgroup.mem_top x)
    rw [hx] at h1
    exact absurd h1 (by decide)
  · rw [eq_bot_iff]
    intro n hn
    have h1 : n ^ 3 = 1 := center_pow_three_of_list hl hq n (hcen hn)
    have h2 : orderOf n ∣ 3 := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf n = 1 := Nat.Coprime.eq_one_of_dvd (hN n hn) h2
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.1 h3

end CFSG.Quasithin.SzN18
