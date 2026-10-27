module

public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem split_inf_eq_bot {K R : Subgroup G} (hKsimp : IsSimpleGroup ↥K)
    (hKeven : Even (Nat.card K)) (hRodd : Odd (Nat.card R))
    (hRnorm : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R) : K ⊓ R = ⊥ := by
  haveI hn : ((K ⊓ R).subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨K.mul_mem (K.mul_mem g.2 hn.1) (K.inv_mem g.2), hRnorm _ g.2 _ hn.2⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ R).subgroupOf K) with h | h
  · rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : ↥K) ∈ (K ⊓ R).subgroupOf K := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    have hle : K ≤ K ⊓ R := Subgroup.subgroupOf_eq_top.mp h
    have hdvd : Nat.card K ∣ Nat.card R := Subgroup.card_dvd_of_le (hle.trans inf_le_right)
    exact (Nat.not_even_iff_odd.mpr hRodd)
      (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp hKeven) hdvd))

theorem split_comm {K R : Subgroup G} (hKsimp : IsSimpleGroup ↥K)
    (hKeven : Even (Nat.card K)) (hRodd : Odd (Nat.card R))
    (hRnorm : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R) (hRK : ∀ r ∈ R, r ∈ Nor K)
    {k r : G} (hk : k ∈ K) (hr : r ∈ R) : k * r = r * k := by
  have hbot := split_inf_eq_bot hKsimp hKeven hRodd hRnorm
  have h1 : k * r * k⁻¹ * r⁻¹ ∈ R := R.mul_mem (hRnorm k hk r hr) (R.inv_mem hr)
  have h2 : k * (r * k⁻¹ * r⁻¹) ∈ K := by
    refine K.mul_mem hk ?_
    have := (Subgroup.mem_normalizer_iff.mp (hRK r hr) k⁻¹).mp (K.inv_mem hk)
    simpa using this
  have h3 : k * r * k⁻¹ * r⁻¹ = k * (r * k⁻¹ * r⁻¹) := by group
  have : k * r * k⁻¹ * r⁻¹ ∈ K ⊓ R := ⟨h3 ▸ h2, h1⟩
  rw [hbot, Subgroup.mem_bot] at this
  calc k * r = k * r * k⁻¹ * r⁻¹ * (r * k) := by group
    _ = r * k := by rw [this, one_mul]

theorem split_two_elt {K R : Subgroup G} (hKsimp : IsSimpleGroup ↥K)
    (hKeven : Even (Nat.card K)) (hRodd : Odd (Nat.card R))
    (hRnorm : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R) (hRK : ∀ r ∈ R, r ∈ Nor K)
    {k r : G} (hk : k ∈ K) (hr : r ∈ R) {n : ℕ} (hx : (k * r) ^ (2 ^ n) = 1) : k * r ∈ K := by
  have hbot := split_inf_eq_bot hKsimp hKeven hRodd hRnorm
  have hc : Commute k r := split_comm hKsimp hKeven hRodd hRnorm hRK hk hr
  rw [hc.mul_pow] at hx
  have h1 : r ^ (2 ^ n) ∈ K ⊓ R :=
    ⟨by rw [eq_inv_of_mul_eq_one_right hx]; exact K.inv_mem (K.pow_mem hk _), R.pow_mem hr _⟩
  rw [hbot, Subgroup.mem_bot] at h1
  have hd : orderOf r ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf r ∣ Nat.card R := by
    have := Subgroup.orderOf_dvd_natCard R hr
    exact this
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  have hr1 : r = 1 := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero] at hm
      exact orderOf_eq_one_iff.mp hm
    · exfalso
      have h2 : 2 ∣ orderOf r := by
        rw [hm]; exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hpos)
      have : 2 ∣ Nat.card R := dvd_trans h2 hd2
      exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr this)
  rw [hr1, mul_one]; exact hk

theorem oupp_two_eq_of_split {X K R : Subgroup G} (hKX : K ≤ X) (hRX : R ≤ X)
    (hKsimp : IsSimpleGroup ↥K) (hKeven : Even (Nat.card K)) (hRodd : Odd (Nat.card R))
    (hRnorm : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R) (hRK : ∀ r ∈ R, r ∈ Nor K)
    (hgen : ∀ x ∈ X, ∃ k ∈ K, ∃ r ∈ R, x = k * r) : OUpp 2 X = K := by
  have hXK : ∀ x ∈ X, x ∈ Nor K := by
    intro x hx
    obtain ⟨k, hk, r, hr, rfl⟩ := hgen x hx
    refine (Nor K).mul_mem ?_ (hRK r hr)
    exact Subgroup.le_normalizer hk
  set S : Set ↥X := {g : ↥X | ∃ k : ℕ, g ^ (2 ^ k) = 1} with hS
  have hOU : OUpp 2 X = (Subgroup.normalClosure S).map X.subtype := rfl
  rw [hOU]
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    haveI : (Subgroup.comap X.subtype K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_comap] at hn ⊢
      have := (Subgroup.mem_normalizer_iff.mp (hXK g g.2) n).mp hn
      exact this
    refine Subgroup.normalClosure_le_normal ?_
    intro g ⟨n, hg⟩
    obtain ⟨k, hk, r, hr, hkr⟩ := hgen g g.2
    have hg' : (g : G) ^ (2 ^ n) = 1 := by
      have := congrArg Subtype.val hg
      simpa using this
    rw [hkr] at hg'
    show (g : G) ∈ K
    rw [hkr]
    exact split_two_elt hKsimp hKeven hRodd hRnorm hRK hk hr hg'
  ·
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 2
      (even_iff_two_dvd.mp hKeven)
    set N := Subgroup.normalClosure S with hN
    haveI hNn : ((N.map X.subtype).subgroupOf K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨y, hy, hyn⟩ := Subgroup.mem_map.mp hn
      refine Subgroup.mem_map.mpr
        ⟨(⟨(g : G), hKX g.2⟩ : ↥X) * y * (⟨(g : G), hKX g.2⟩ : ↥X)⁻¹,
          (inferInstance : N.Normal).conj_mem y hy _, ?_⟩
      have hyn' : (y : G) = n := hyn
      simp [hyn']
    have htS : (⟨(t : G), hKX t.2⟩ : ↥X) ∈ S := by
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have : (t : ↥K) ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
      simpa using congrArg Subtype.val this
    have htN : (t : G) ∈ N.map X.subtype :=
      Subgroup.mem_map.mpr ⟨_, Subgroup.subset_normalClosure htS, rfl⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.map X.subtype).subgroupOf K) with h | h
    · exfalso
      have : t ∈ (N.map X.subtype).subgroupOf K := htN
      rw [h, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at ht
      omega
    · intro x hx
      have : (⟨x, hx⟩ : ↥K) ∈ (N.map X.subtype).subgroupOf K := by rw [h]; trivial
      exact this

end CFSG.RankThree.PartTwo.Sec21.FF79
