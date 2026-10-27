module

public import CFSG.Quasithin.Vol2.Ch10SecKRRc
public import CFSG.Quasithin.Vol2.Ch10SecKRRd
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyOddRankOneGlue
public import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KRR

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def RankWit {X : Type} [Group X] [Finite X] (B L : Subgroup X) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (ModO2 B) ∧ 2 ≤ CFSG.Open.pRank p L

@[expose] def RankGoal {X : Type} [Group X] [Finite X] (B L : Subgroup X) : Prop :=
  (((∃ n : ℕ, CFSG.Blueprint.SuzukiModel (ModO2 B) 2 n) ∨
        Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) →
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (ModO2 B) ∧ 2 ≤ CFSG.Open.pRank p L) ∧
    ((Nonempty (ModO2 B ≃* alternatingGroup (Fin 5)) ∨
        ∃ n : ℕ, 2 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
          Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (ModO2 B) ∧ 2 ≤ CFSG.Open.pRank p L) ∨
        (CFSG.pCore 2 ↥B = ⊥ ∧ (A312C8 B L ∨ A312C15 B L)))

theorem RankWit.goal {X : Type} [Group X] [Finite X] {B L : Subgroup X} (h : RankWit B L) :
    RankGoal B L :=
  ⟨fun _ => h, fun _ => Or.inl h⟩

theorem rankWit_of {X : Type} [Group X] [Finite X] {B L : Subgroup X} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hB : r ∣ Nat.card B) (hL : 2 ≤ CFSG.Open.pRank r L) : RankWit B L :=
  ⟨r, hr, hr2, dvd_card_modO2 hr hr2 hB, hL⟩

theorem card_sl3_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(StatedSL 3 K) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_of_card_eq_two hK

theorem not_dvd_168 {n : ℕ} (hn : 2 ≤ n) : ¬ 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ 168 := by
  intro h
  have hle := Nat.le_of_dvd (by norm_num) h
  have hn4 : n < 4 := by
    by_contra h4
    push Not at h4
    have h16 : 16 ≤ 2 ^ n :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h4
    have h2 : 16 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h16 2
    have : 16 * (16 ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_le_mul h16 (Nat.sub_le_sub_right h2 1)
    omega
  interval_cases n <;> norm_num at h

theorem three_dvd_four_pow_sub_one (n : ℕ) : 3 ∣ (2 ^ n) ^ 2 - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow 4 1 n
  rw [one_pow, show (4 : ℕ) - 1 = 3 by rfl] at h
  rwa [← pow_mul, mul_comm, pow_mul, show (2 : ℕ) ^ 2 = 4 by rfl]

section C2


theorem rankWit_C2 (hLF : A312LeviField) {X : Type} [Group X] [Finite X] {B L : Subgroup X}
    (h : A312C2 B L) : RankWit B L := by
  obtain ⟨f, n, hfn, hB, hL⟩ := hLF X B L h
  obtain ⟨-, -, P, hP, hBP⟩ := h
  have hn2 : 2 ≤ n := by
    obtain ⟨-, hn1, -, h22, -⟩ := hB.1
    by_contra hlt
    have : n = 1 := by omega
    subst this
    exact h22 rfl
  have hN : Nat.card (ModO2 B) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := card_of_isPSL_two_two hB
  have hdvd : ∀ r, r ∣ 2 ^ f - 1 → r ∣ Nat.card (ModO2 B) := fun r hr => by
    rw [hN]
    have h1 : 2 ^ f - 1 ∣ 2 ^ n - 1 := by
      obtain ⟨k, rfl⟩ := hfn
      have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 k
      rwa [one_pow, ← pow_mul] at this
    have h2 : 2 ^ n - 1 ∣ (2 ^ n) ^ 2 - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
      rwa [one_pow] at this
    exact Dvd.dvd.mul_left (hr.trans (h1.trans h2)) _
  have h3 : 3 ∣ Nat.card (ModO2 B) := by
    rw [hN]
    exact Dvd.dvd.mul_left (three_dvd_four_pow_sub_one n) _
  have hBL : B ≤ L := hBP ▸ (perfectCore_le P).trans hP.1.1
  have hNL : Nat.card (ModO2 B) ∣ Nat.card L :=
    (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_dvd_of_le hBL)
  rcases hL with ⟨hf1, hm⟩ | ⟨hf1, hm⟩ | ⟨hf2, hm⟩ | ⟨hf2, hm⟩ | ⟨hf1, hm⟩ | ⟨-, hf3, hm⟩
  · by_cases hf2 : 2 ≤ f
    · obtain ⟨r, hr, hr2, hrd, hrank⟩ := exists_two_le_pRank_psl3_two hf2 hm
      exact ⟨r, hr, hr2, hdvd r hrd, two_le_open_pRank_of_mulEquiv hr (MulEquiv.refl _) hrank⟩
    · exfalso
      obtain rfl : f = 1 := by omega
      rw [card_of_isPSL_three_two hm, hN] at hNL
      exact not_dvd_168 hn2 hNL
  · by_cases hf2 : 2 ≤ f
    · obtain ⟨r, hr, hr2, hrd⟩ := CFSG.RankThree.Chevalley.exists_odd_prime_dvd_two_pow_sub_one hf2
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
      exact ⟨r, hr, hr2, hdvd r hrd, two_le_open_pRank_of_mulEquiv hr e
        (two_le_pRank_sl3_torus hr (by rw [hK]; exact hrd))⟩
    · exfalso
      obtain rfl : f = 1 := by omega
      obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
      rw [Nat.card_congr e.toEquiv, card_sl3_of_card_two (by rw [hK]; rfl), hN] at hNL
      exact not_dvd_168 hn2 hNL
  · obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := hm
    refine ⟨3, Nat.prime_three, by norm_num, h3,
      two_le_open_pRank_of_mulEquiv Nat.prime_three e ?_⟩
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psp le_rfl
  · obtain ⟨r, hr, hr2, hrd⟩ := CFSG.RankThree.Chevalley.exists_odd_prime_dvd_two_pow_sub_one hf2
    exact ⟨r, hr, hr2, hdvd r hrd, two_le_open_pRank_of_mulEquiv hr (MulEquiv.refl _)
      (two_le_pRank_G2_of_dvd hr hrd hm.2)⟩
  · by_cases hf2 : 2 ≤ f
    · obtain ⟨r, hr, hr2, hrd⟩ :=
        CFSG.RankThree.Chevalley.exists_odd_prime_dvd_two_pow_sub_one hf2
      exact ⟨r, hr, hr2, hdvd r hrd, two_le_open_pRank_of_mulEquiv hr (MulEquiv.refl _)
        (two_le_pRank_3D4_of_dvd hf1 hr hrd hm.2)⟩
    · obtain rfl : f = 1 := by omega
      exact ⟨3, Nat.prime_three, by norm_num, h3,
        two_le_open_pRank_of_mulEquiv Nat.prime_three (MulEquiv.refl _)
          (CFSG.QuasithinUnique.Setup.Family.trialityTwoHasRankTwo ↥L hm)⟩
  · obtain ⟨r, hr, hr2, hrd⟩ :=
      CFSG.RankThree.Chevalley.exists_odd_prime_dvd_two_pow_sub_one (by omega : 2 ≤ f)
    exact ⟨r, hr, hr2, hdvd r hrd, two_le_open_pRank_of_mulEquiv hr (MulEquiv.refl _)
      (two_le_pRank_2F4_of_dvd hm hr hrd)⟩

end C2

section C3


theorem rankWit_C3 {X : Type} [Group X] [Finite X] {B L : Subgroup X} (h : A312C3 B L) :
    RankWit B L := by
  obtain ⟨f, hSz, hL, -⟩ := h
  obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := hSz
  obtain ⟨r, hr, hr2, hrd⟩ :=
    CFSG.RankThree.Chevalley.exists_odd_prime_dvd_two_pow_sub_one (by omega : 2 ≤ f)
  refine ⟨r, hr, hr2, ?_, two_le_open_pRank_of_mulEquiv hr (MulEquiv.refl _)
    (two_le_pRank_2F4_of_dvd hL hr hrd)⟩
  rw [hf] at hK hrd
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hrd _) _

end C3

theorem rankWit_C4 {X : Type} [Group X] [Finite X] {B L : Subgroup X} (h : A312C4 B L) :
    RankWit B L := by
  obtain ⟨hB, hL, -⟩ := h
  have h3 : 3 ∣ Nat.card (ModO2 B) := by rw [card_of_isPSL_three_two hB]; norm_num
  rcases hL with hL | hL
  · exact ⟨3, Nat.prime_three, by norm_num, h3, two_le_pRank_three_of_isPSL_two_one le_rfl hL⟩
  · exact ⟨3, Nat.prime_three, by norm_num, h3,
      two_le_pRank_three_of_isPSL_two_one (by norm_num) hL⟩

theorem rankWit_C5 {X : Type} [Group X] [Finite X] {B L : Subgroup X} (h : A312C5 B L) :
    RankWit B L := by
  obtain ⟨hB, hL, -⟩ := h
  exact ⟨3, Nat.prime_three, by norm_num, by rw [card_of_isPSL_four_two hB]; norm_num,
    two_le_pRank_three_of_isPSL_two_one (by norm_num) hL⟩

end CFSG.Quasithin.Vol2.Ch10.SecB.KRR
