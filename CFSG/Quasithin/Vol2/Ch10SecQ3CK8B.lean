module

public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

section Num

theorem sl2_ne {n N : ℕ} (hN : N = 2520 ∨ N = 7560) : (2 ^ n) * ((2 ^ n) ^ 2 - 1) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> norm_num at h <;> omega
  · have hq : 32 ≤ 2 ^ n := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 32 * (32 ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega

theorem sl3_ne {n N : ℕ} (hN : N = 2520 ∨ N = 7560) :
    (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h <;> omega
  · have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 4 ^ 3 * ((4 ^ 2 - 1) * (4 ^ 3 - 1)) ≤
        (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
    omega

theorem sp4_ne {n N : ℕ} (hN : N = 2520 ∨ N = 7560) :
    (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h <;> omega
  · have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 4 ^ (2 ^ 2) * (((4 ^ 2 - 1)) * (4 ^ 4 - 1)) ≤
        (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq _)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1))
    omega

theorem g2_ne {n N : ℕ} (hN : N = 2520 ∨ N = 7560) :
    (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 1 with hn | hn
  · have h0 : n = 0 := by omega
    subst h0
    norm_num at h
    omega
  · have hq : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 2 ^ 6 * ((2 ^ 6 - 1) * (2 ^ 2 - 1)) ≤
        (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
    omega

end Num

section Models

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem not_sl2 (hN : Nat.card ↥L = 2520 ∨ Nat.card ↥L = 7560) {n : ℕ}
    (h : BinaryNaturalSL L U Z 2 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hc := card_eq_of_nat_realizes1527d hπ
  rw [card_statedSL_two1527d, hF] at hc
  exact sl2_ne hN hc.symm

theorem not_sl3 (hN : Nat.card ↥L = 2520 ∨ Nat.card ↥L = 7560) {n : ℕ}
    (h : BinaryNaturalSL L U Z 3 n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hc := card_eq_of_nat_realizes1527d hπ
  rw [card_statedSL_three1527d, hF] at hc
  exact sl3_ne hN hc.symm

theorem not_sp4 (hN : Nat.card ↥L = 2520 ∨ Nat.card ↥L = 7560) {n : ℕ}
    (h : BinaryNaturalSp4 L U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hc := card_eq_of_nat_realizes1527d hπ
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  have hX : Nat.card ↥(StatedSp 2 F) =
      (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
    rw [hI, Finset.prod_pair (by norm_num)]
  rw [hX] at hc
  exact sp4_ne hN hc.symm

theorem not_g2 (hN : Nat.card ↥L = 2520 ∨ Nat.card ↥L = 7560) {n : ℕ}
    (h : G2Natural L U Z n) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.quasithinG2 F) := by
    have := FFC.charP_two_of_card_pow hF
    exact (Nat.card_congr (Equiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
  rw [card_quasithinG2_1527d hF, hF] at hcard
  exact g2_ne hN hcard.symm

theorem not_g2d (hN : Nat.card ↥L = 2520 ∨ Nat.card ↥L = 7560)
    (h : G2NaturalDerived L U Z 1) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hG2 := card_quasithinG2_1527d hF
  rw [hF] at hG2
  have hfin : Finite ↥(CFSG.Open.quasithinG2 F) :=
    Nat.finite_of_card_ne_zero (by rw [hG2]; norm_num)
  have h1 : Nat.card ↥L ∣
      Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
    Subgroup.card_dvd_of_surjective hπ.1
  have h2 : Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ ∣
      Nat.card ↥(CFSG.Open.quasithinG2 F) := by
    refine Subgroup.card_dvd_of_le ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (CFSG.Open.quasithinG2 F).mul_mem
      ((CFSG.Open.quasithinG2 F).mul_mem ((CFSG.Open.quasithinG2 F).mul_mem ha hb)
        ((CFSG.Open.quasithinG2 F).inv_mem ha)) ((CFSG.Open.quasithinG2 F).inv_mem hb)
  have h3 := h1.trans h2
  rw [hG2] at h3
  have h5 : 5 ∣ Nat.card ↥L := by rcases hN with h | h <;> rw [h] <;> norm_num
  have := h5.trans h3
  norm_num at this

theorem not_surj_sl {d : ℕ} (hd : d = 4 ∨ d = 5) (hN : Nat.card ↥L = 2520 ∨ Nat.card ↥L = 7560)
    (π : ↥(StatedSL d (ZMod 2)) →* ↥L) (hπ : Function.Surjective π) : False := by
  have hs := B69.isSimpleGroup_statedSL_two (K := ZMod 2) (Nat.card_zmod 2) (n := d)
    (by omega)
  rcases hs.eq_bot_or_eq_top_of_normal π.ker with hk | hk
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hk
    have hc := (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)).symm
    rcases hd with rfl | rfl
    · rw [card_statedSL_four_zmod1527d] at hc
      omega
    · rw [card_statedSL_five_zmod1527d] at hc
      omega
  · have h1 : Nat.card ↥L = 1 := by
      refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => ?_⟩, ⟨1⟩⟩
      obtain ⟨a, rfl⟩ := hπ x
      obtain ⟨b, rfl⟩ := hπ y
      rw [MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top a),
        MonoidHom.mem_ker.1 (hk ▸ Subgroup.mem_top b)]
    omega

end Models

end CFSG.Quasithin.Vol2.Ch10.SecB.C11AmS.K8
