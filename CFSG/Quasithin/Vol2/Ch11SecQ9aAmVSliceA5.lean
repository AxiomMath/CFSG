module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmVSlice
public import CFSG.Quasithin.Recognition.GoldschmidtF112A5
public import CFSG.Quasithin.Background.F918Z8Op4d
public import CFSG.Quasithin.Background.HSU3Borel
public import CFSG.Quasithin.SteinbergBYEvenUnitaryTwoThreeControl
public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmV

public section

namespace CFSG.Quasithin

open CFSG.Open

private theorem eq_two_of_psl_card_sixty {f : ℕ} (hf : 1 ≤ f) (hc : 2 ^ f * (4 ^ f - 1) = 60) :
    f = 2 := by
  by_contra hne
  rcases Nat.lt_or_ge f 2 with h1 | h2
  · obtain rfl : f = 1 := by omega
    norm_num at hc
  · have h3 : 3 ≤ f := by omega
    have h8 : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have h64 : 64 ≤ 4 ^ f := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have : 8 * 63 ≤ 2 ^ f * (4 ^ f - 1) := Nat.mul_le_mul h8 (by omega)
    omega

private theorem sz_eq_suzukiMatrixGroup_A5 (n : ℕ) :
    Sz n = CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n :=
  (show CFSG.Theory.Comparator.SzModel n = Sz n by
      simp only [CFSG.Theory.Comparator.SzModel, CFSG.Theory.Comparator.SzGenerators, CFSG.Open.Sz,
        CFSG.Open.SzGenerators]).symm.trans (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n)

private theorem card_ne_sixty_of_sz (a : ℕ) {K : Type} [Group K] (e : K ≃* ↥(Sz a)) :
    Nat.card K ≠ 60 := by
  intro h60
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [Nat.card_congr e.toEquiv, card_sz_zero] at h60
    omega
  · rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (MulEquiv.subgroupCongr (sz_eq_suzukiMatrixGroup_A5 a)).toEquiv,
      opq4d_card_suzukiMatrixGroup (m := a) (by omega)] at h60
    have h8 : 8 ≤ 2 ^ (2 * a + 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h64 : 64 ≤ (2 ^ (2 * a + 1)) ^ 2 := by
      calc 64 = 8 ^ 2 := by norm_num
        _ ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.pow_le_pow_left h8 2
    have hpos : 1 ≤ (2 ^ (2 * a + 1)) ^ 2 + 1 := by omega
    have h7 : 7 ≤ 2 ^ (2 * a + 1) - 1 := by omega
    have hbig : 1 * 64 * 7 ≤
        ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hpos h64) h7
    omega

private theorem not_eight_dvd_sixty_of_two_pow_cube {n : ℕ} (hn : 1 ≤ n)
    (hd : (2 ^ n) ^ 3 ∣ 60) : False := by
  have h8 : 8 ∣ (2 ^ n) ^ 3 := by
    rw [← pow_mul]
    have h8' : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8']
    exact pow_dvd_pow 2 (by omega)
  have h860 : 8 ∣ 60 := h8.trans hd
  norm_num at h860

theorem isL2Quot_two_of_listed_card_sixty {K : Type} [Group K] (hK : IsRankOneListed K)
    (h60 : Nat.card K = 60) : IsL2Quot 2 K := by
  rcases hK with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  ·
    have hX : IsL2Quot n K := ⟨e⟩
    have hc := hX.card hn
    rw [h60] at hc
    obtain rfl : n = 2 := eq_two_of_psl_card_sixty hn hc.symm
    exact ⟨e⟩
  ·
    exact (card_ne_sixty_of_sz a e h60).elim
  ·
    have hc : Nat.card K = Nat.card (StatedSU 3 (2 ^ n) F) := Nat.card_congr e.toEquiv
    have h2 := H.SU3.card_statedSU_two (K := F) hn hF
    rw [← hc, h60] at h2
    have hd : (2 ^ n) ^ 3 ∣ 60 := by
      rw [← h2]
      exact Nat.ordProj_dvd 60 2
    exact (not_eight_dvd_sixty_of_two_pow_cube hn hd).elim
  ·
    have hc : Nat.card K = Nat.card (StatedProj (StatedSU 3 (2 ^ n) F)) :=
      Nat.card_congr e.toEquiv
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · obtain rfl : n = 1 := by omega
      rw [card_statedProj_one hF] at hc
      omega
    · obtain ⟨r, hr, -, -⟩ := SteinbergBY.card_PSU3_arith h2 hF
      have hd : (2 ^ n) ^ 3 ∣ 60 := ⟨r, by rw [← hr, ← hc, h60]⟩
      exact (not_eight_dvd_sixty_of_two_pow_cube hn hd).elim
  ·
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card] at h60
    exact absurd h60 (by norm_num)

theorem vA5_of_listed_card_sixty {G : Type} [Group G] {L : Subgroup G}
    (hL : IsRankOneListed (oTwoQuot ↥L)) (h60 : Nat.card (oTwoQuot ↥L) = 60) :
    F112R.VA5 L :=
  isL2Quot_two_of_listed_card_sixty hL h60

theorem f112L24G2_of_A5 (h : F112R.F112SliceA5) : F112L24G2Statement := by
  intro G _ _ L1 L2 S hyp hQ hS h1 h2 hb
  obtain ⟨L1', L2', hsw, -, hlist, -⟩ :=
    h G L1 L2 S ⟨hyp, hQ, hS⟩
      (Or.inl ⟨vA5_of_listed_card_sixty hyp.h1.listed h1,
        vA5_of_listed_card_sixty hyp.h2.listed h2⟩)
  refine ⟨L1', L2', hsw, ?_⟩
  rcases hsw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact F112L24G2.isG2_of_f112List hlist h1 h2 hb
  · exact F112L24G2.isG2_of_f112List hlist h2 h1 hb.symm

end CFSG.Quasithin

end
