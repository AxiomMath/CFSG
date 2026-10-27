module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

private theorem card_sylow_five_eq_five {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H ∣ 40) (h5 : 5 ∣ Nat.card H) (P : Sylow 5 H) : Nat.card P = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hk : (Nat.card H).factorization 5 = 1 := by
    have hdvd : 5 ^ (Nat.card H).factorization 5 ∣ 40 := (Nat.ordProj_dvd _ _).trans hH
    have hpos : 0 < (Nat.card H).factorization 5 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_five (Nat.card_pos.ne') h5
    by_contra hne
    have h2 : 2 ≤ (Nat.card H).factorization 5 := by omega
    have : 5 ^ 2 ∣ 40 := (pow_dvd_pow 5 h2).trans hdvd
    norm_num at this
  rw [Sylow.card_eq_multiplicity, hk]
  norm_num

private theorem eq_one_of_dvd_eight_of_modEq_one {n : ℕ} (h8 : n ∣ 8) (hmod : n ≡ 1 [MOD 5]) :
    n = 1 := by
  have hle : n ≤ 8 := Nat.le_of_dvd (by norm_num) h8
  unfold Nat.ModEq at hmod
  interval_cases n <;> first | rfl | omega

private theorem subsingleton_sylow_five {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H ∣ 40) (h5 : 5 ∣ Nat.card H) : Subsingleton (Sylow 5 H) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P, -⟩ : ∃ P : Sylow 5 H, (⊥ : Subgroup H) ≤ P := IsPGroup.of_bot.exists_le_sylow
  have hcard : Nat.card (P : Subgroup H) = 5 := card_sylow_five_eq_five hH h5 P
  have hi : Nat.card (P : Subgroup H) * (P : Subgroup H).index = Nat.card H :=
    Subgroup.card_mul_index _
  have hidx : (P : Subgroup H).index ∣ 8 := by
    have h1 : 5 * (P : Subgroup H).index ∣ 5 * 8 := by
      rw [hcard] at hi
      rw [hi]
      have h40 : (5 : ℕ) * 8 = 40 := by norm_num
      rw [h40]
      exact hH
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hn8 : Nat.card (Sylow 5 H) ∣ 8 := (Sylow.card_dvd_index P).trans hidx
  have hn1 : Nat.card (Sylow 5 H) = 1 :=
    eq_one_of_dvd_eight_of_modEq_one hn8 (card_sylow_modEq_one 5 H)
  exact (Nat.card_eq_one_iff_unique.1 hn1).1

theorem card_dvd_eight_of_pow_three_normalizes {G : Type*} [Group G] [Finite G]
    {T : Subgroup G} {t : G} (ht : t ^ 3 = 1) (htT : t ∈ Subgroup.normalizer (T : Set G))
    (hT : Nat.card T ∣ 40) (hfix : ∀ x ∈ T, orderOf x = 5 → t * x ≠ x * t) :
    Nat.card T ∣ 8 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_cases h5 : 5 ∣ Nat.card T
  · exfalso
    have : Fintype T := Fintype.ofFinite T
    have hsub : Subsingleton (Sylow 5 T) := subsingleton_sylow_five hT h5
    obtain ⟨xT, hxT⟩ := exists_prime_orderOf_dvd_card 5
      (by rw [Nat.card_eq_fintype_card] at h5; exact h5)
    have hxP : IsPGroup 5 (Subgroup.zpowers xT) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxT, pow_one])
    obtain ⟨P0, hP0⟩ := IsPGroup.exists_le_sylow hxP
    have key : ∀ z : T, orderOf z = 5 → z ∈ (P0 : Subgroup T) := by
      intro z hz
      have hzP : IsPGroup 5 (Subgroup.zpowers z) :=
        IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
      obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hzP
      have hQP : Q = P0 := hsub.elim Q P0
      have hz_mem : z ∈ (Q : Subgroup T) := hQ (Subgroup.mem_zpowers z)
      rw [hQP] at hz_mem
      exact hz_mem
    have hPeq : Subgroup.zpowers xT = (P0 : Subgroup T) := by
      apply Subgroup.eq_of_le_of_card_ge hP0
      exact le_of_eq ((card_sylow_five_eq_five hT h5 P0).trans (by rw [Nat.card_zpowers, hxT]))
    have hcT : t * (xT : G) * t⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 htT _).1 xT.2
    have hyord : orderOf (⟨t * (xT : G) * t⁻¹, hcT⟩ : T) = 5 := by
      rw [← Subgroup.orderOf_coe]
      show orderOf (t * (xT : G) * t⁻¹) = 5
      have hc : orderOf (t * (xT : G) * t⁻¹) = orderOf (xT : G) :=
        orderOf_injective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective (xT : G)
      rw [hc, Subgroup.orderOf_coe, hxT]
    have hyP : (⟨t * (xT : G) * t⁻¹, hcT⟩ : T) ∈ Subgroup.zpowers xT := by
      rw [hPeq]
      exact key _ hyord
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyP
    have hk' : (xT : G) ^ k = t * (xT : G) * t⁻¹ := by
      have := congrArg Subtype.val hk
      simpa using this
    have hx5 : orderOf (xT : G) = 5 := by rw [Subgroup.orderOf_coe, hxT]
    have hxT0 : (xT : G) ∈ T := xT.2
    have hx5pow : (xT : G) ^ (5 : ℤ) = 1 := by
      have := pow_orderOf_eq_one (xT : G)
      rw [hx5] at this
      simpa using this
    have hstep : ∀ j : ℤ, t * (xT : G) ^ j * t⁻¹ = ((xT : G) ^ k) ^ j := by
      intro j
      rw [hk', conj_zpow]
    have hthree : ∀ g : G, t * (t * (t * g * t⁻¹) * t⁻¹) * t⁻¹ = g := by
      intro g
      have h3 : t * (t * (t * g * t⁻¹) * t⁻¹) * t⁻¹ = (t * (t * t)) * g * (t * (t * t))⁻¹ := by
        group
      have ht3 : t * (t * t) = 1 := by rw [← pow_three]; exact ht
      rw [ht3] at h3
      simpa using h3
    have hcube : (xT : G) ^ (k * (k * k)) = (xT : G) := by
      have h1 := hthree (xT : G)
      rw [← hk'] at h1
      rw [hstep k, ← zpow_mul] at h1
      rw [hstep (k * k), ← zpow_mul] at h1
      exact h1
    have hpow : (xT : G) ^ (k * (k * k) - 1) = 1 := by
      rw [zpow_sub_one, hcube, mul_inv_cancel]
    have h5d : (5 : ℤ) ∣ k * (k * k) - 1 := by
      have := orderOf_dvd_iff_zpow_eq_one.2 hpow
      rw [hx5] at this
      exact_mod_cast this
    have hz : ((k * (k * k) - 1 : ℤ) : ZMod 5) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).2 (by exact_mod_cast h5d)
    push_cast at hz
    have hz' : (k : ZMod 5) * ((k : ZMod 5) * (k : ZMod 5)) = 1 := sub_eq_zero.1 hz
    have key1 : ∀ a : ZMod 5, a * (a * a) = 1 → a = 1 := by decide
    have hk5 : (k : ZMod 5) = 1 := key1 _ hz'
    have hk1 : ((k - 1 : ℤ) : ZMod 5) = 0 := by
      push_cast
      rw [hk5, sub_self]
    have hd : (5 : ℤ) ∣ k - 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 5).1 hk1
      exact_mod_cast this
    obtain ⟨m, hm⟩ := hd
    have hkm : k = 1 + 5 * m := by linarith
    have hxk : (xT : G) ^ k = (xT : G) := by
      rw [hkm, zpow_add, zpow_mul, hx5pow, one_zpow, mul_one, zpow_one]
    have hcomm : t * (xT : G) * t⁻¹ = (xT : G) := by
      rw [← hk', hxk]
    exact hfix (xT : G) hxT0 hx5 (mul_inv_eq_iff_eq_mul.1 hcomm)
  · have hcop : Nat.Coprime (Nat.card T) 5 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5)
    have h40 : Nat.card T ∣ 8 * 5 := by norm_num; exact hT
    exact hcop.dvd_of_dvd_mul_right h40

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

end
