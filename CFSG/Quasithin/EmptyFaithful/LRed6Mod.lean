module

public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace LRed6

@[expose] def InS (N : ℕ) : Prop := N = 360 ∨ N = 1080 ∨ N = 2520 ∨ N = 6048

theorem inS_lt {N : ℕ} (h : InS N) : N ≤ 6048 := by
  rcases h with rfl | rfl | rfl | rfl <;> norm_num

theorem sl2_num {n N : ℕ} (hN : InS N) : (2 ^ n) * ((2 ^ n) ^ 2 - 1) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 6 with hn | hn
  · interval_cases n <;> norm_num at h <;> rcases hN with rfl | rfl | rfl | rfl <;> omega
  · have hq : 64 ≤ 2 ^ n := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 64 * (64 ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    have h2 := inS_lt hN
    omega

theorem sl3_num {n N : ℕ} (hN : InS N) :
    (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num at h <;> rcases hN with rfl | rfl | rfl | rfl <;> omega
  · have hq : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 8 ^ 3 * ((8 ^ 2 - 1) * (8 ^ 3 - 1)) ≤
        (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
    have h2 := inS_lt hN
    omega

theorem sp4_num {n N : ℕ} (hN : InS N) :
    (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num at h <;> rcases hN with rfl | rfl | rfl | rfl <;> omega
  · have hq : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 4 ^ (2 ^ 2) * (((4 ^ 2 - 1)) * (4 ^ 4 - 1)) ≤
        (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq _)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1))
    have h2 := inS_lt hN
    omega

theorem g2_num {n N : ℕ} (hN : InS N) :
    (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) ≠ N := by
  intro h
  rcases Nat.lt_or_ge n 1 with hn | hn
  · have h0 : n = 0 := by omega
    subst h0
    norm_num at h
    rcases hN with rfl | rfl | rfl | rfl <;> omega
  · have hq : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h1 : 2 ^ 6 * ((2 ^ 6 - 1) * (2 ^ 2 - 1)) ≤
        (2 ^ n) ^ 6 * (((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 2 - 1)) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hq 6)
        (Nat.mul_le_mul (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 6) 1)
          (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
    have h2 := inS_lt hN
    omega

theorem card_of_surj_sl_two {d : ℕ} (hd : 3 ≤ d) {L : Type} [Group L] (π : ↥(StatedSL d (ZMod 2)) →* L)
    (hπ : Function.Surjective π) :
    Nat.card L = 1 ∨ Nat.card L = Nat.card ↥(StatedSL d (ZMod 2)) := by
  have hs := CFSG.Quasithin.B69.isSimpleGroup_statedSL_two (K := ZMod 2) (Nat.card_zmod 2) hd
  rcases hs.eq_bot_or_eq_top_of_normal π.ker with hk | hk
  · right
    have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hk
    exact (Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ⟩)).symm
  · left
    have : Subsingleton L := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := hπ x
      obtain ⟨b, rfl⟩ := hπ y
      have ha : a ∈ π.ker := hk ▸ Subgroup.mem_top a
      have hb : b ∈ π.ker := hk ▸ Subgroup.mem_top b
      rw [MonoidHom.mem_ker] at ha hb
      rw [ha, hb]⟩
    exact Nat.card_unique

theorem modelShape_of_card {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {U Z : Subgroup V}
    (hL : InS (Nat.card ↥L)) (h : B42ModulePair L U Z) :
    AlternatingNatural L U Z 6 ∨ AlternatingNatural L U Z 7 ∨ A7Four L U Z ∨ TripleA6Six L U Z ∨
      G2NaturalDerived L U Z 1 := by
  rcases h with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h | h | h | h | h | h | h
  ·
    exfalso
    obtain ⟨F, _, _, hF, π, hπ⟩ := h
    have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_two1527d, hF] at hc
    exact sl2_num hL hc.symm
  ·
    exfalso
    obtain ⟨F, _, _, hF, π, hπ⟩ := h
    have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL_three1527d, hF] at hc
    exact sl3_num hL hc.symm
  ·
    exfalso
    obtain ⟨F, _, _, hF, π, hπ⟩ := h
    have hc := card_eq_of_nat_realizes1527d hπ
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    have hX : Nat.card ↥(StatedSp 2 F) =
        (2 ^ n) ^ (2 ^ 2) * ((((2 ^ n) ^ 2 - 1)) * ((2 ^ n) ^ 4 - 1)) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hF]
      rw [hI, Finset.prod_pair (by norm_num)]
    rw [hX] at hc
    exact sp4_num hL hc.symm
  ·
    exfalso
    obtain ⟨F, _, _, hF, π, hπ⟩ := h
    have hcard : Nat.card ↥L = Nat.card ↥(CFSG.Open.quasithinG2 F) := by
      have := FFC.charP_two_of_card_pow hF
      exact (Nat.card_congr (Equiv.ofBijective π
        ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
    rw [card_quasithinG2_1527d hF, hF] at hcard
    exact g2_num hL hcard.symm
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  ·
    exfalso
    obtain ⟨π, hπ⟩ := h
    have h1 : Nat.card ↥L ≤ Nat.card ↥(alternatingGroup (Fin 5)) :=
      Nat.card_le_card_of_surjective π hπ.1
    rw [card_alternatingGroup1527d 5 (by norm_num)] at h1
    norm_num [Nat.factorial] at h1
    rcases hL with h | h | h | h <;> omega
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  ·
    exfalso
    obtain ⟨F, _, _, hF, π, hπ⟩ := h
    have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL1527d (by norm_num), hF] at hc
    norm_num [Finset.prod_Icc_succ_top] at hc
    rcases hL with h | h | h | h <;> omega
  ·
    exfalso
    obtain ⟨F, _, _, hF, π, hπ⟩ := h
    have hc := card_eq_of_nat_realizes1527d hπ
    rw [card_statedSL1527d (by norm_num), hF] at hc
    norm_num [Finset.prod_Icc_succ_top] at hc
    rcases hL with h | h | h | h <;> omega
  ·
    exfalso
    obtain ⟨π, hπ⟩ := h
    rcases card_of_surj_sl_two (by norm_num) π hπ.1 with h1 | h1
    · rcases hL with h | h | h | h <;> omega
    · rw [card_statedSL_four_zmod1527d] at h1
      rcases hL with h | h | h | h <;> omega
  ·
    exfalso
    obtain ⟨π, hπ⟩ := h
    rcases card_of_surj_sl_two (by norm_num) π hπ.1 with h1 | h1
    · rcases hL with h | h | h | h <;> omega
    · rw [card_statedSL_five_zmod1527d] at h1
      rcases hL with h | h | h | h <;> omega

end LRed6

end CFSG.Quasithin
