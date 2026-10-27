module

public import CFSG.Quasithin.Vol2.Ch11SecA02Recog
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.Vol2.Ch11SecABasicV
public import CFSG.Quasithin.Background.C4Defs
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL)

theorem card_SL3_oSL3 {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) = 2 ^ (3 * m) * oSL3 m := by
  rw [CFSG.BrauerLinearThree.card_SL_three, mul_assoc, hK, oSL3]
  ring_nf

theorem card_Sp4_oSp4 {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(StatedSp 2 K) = 2 ^ (4 * n) * oSp4 n := by
  rw [LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  rw [hI, Finset.prod_pair (by norm_num), hK, oSp4]
  ring_nf

theorem card_G2_oG2 (hG2 : FactG2DerivedOrder) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥⁅quasithinG2 K, quasithinG2 K⁆ = 2 ^ (6 * n) * oG2 n := by
  rw [hG2 K n hn hK, oG2]
  ring_nf

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem card_quot_eq_card_autOn (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card ↥(autOn L (fsuV T I)) := by
  obtain ⟨_, -, -, ⟨e⟩, -⟩ := h1102 G T L I n h
  exact Nat.card_congr e.toEquiv

theorem card_quot_cases (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    (KindSL3 L (fsuV T I) n ∧ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ (3 * n) * oSL3 n) ∨
      (KindSp4 L (fsuV T I) n ∧ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ (4 * n) * oSp4 n) ∨
      (KindG2 L (fsuV T I) n ∧ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ (6 * n) * oG2 n) := by
  rw [card_quot_eq_card_autOn h1102 h]
  rcases kind_cases h1102 h with hk | hk | hk
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hk
    exact Or.inl ⟨⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩,
      (Nat.card_congr e.toEquiv).trans (card_SL3_oSL3 hK)⟩
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hk
    exact Or.inr (Or.inl ⟨⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩,
      (Nat.card_congr e.toEquiv).trans (card_Sp4_oSp4 hK)⟩)
  · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hk
    exact Or.inr (Or.inr ⟨⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩,
      (Nat.card_congr e.toEquiv).trans (card_G2_oG2 hG2 h.one_lt hK)⟩)

theorem two_pow_six_dvd_card_quot (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) : 2 ^ 6 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hn : 2 ≤ n := h.one_lt
  rcases card_quot_cases hG2 h1102 h with ⟨-, hc⟩ | ⟨-, hc⟩ | ⟨-, hc⟩ <;> rw [hc] <;>
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) _

theorem card_quot_ne (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    {N : ℕ} (hN : ¬ 2 ^ 6 ∣ N) : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≠ N := by
  intro hc
  exact hN (hc ▸ two_pow_six_dvd_card_quot hG2 h1102 h)

omit [Finite G] in
theorem card_quot_of_modO2Surj {H : Type} [Group H] {α : ↥L →* H} (hα : IsModO2Surj L α) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card H :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hα.2.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hα.1)).toEquiv

theorem card_of_isPSU_three {X : Type} [Group X] (hX : IsPSU 3 3 1 X) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hX

theorem not_isG2Block (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    ¬ IsG2Block L := fun hB =>
  card_quot_ne hG2 h1102 h (N := 6048) (by norm_num) (card_of_isPSU_three hB.2.1)

theorem not_isAltBlockType_six (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) : ¬ IsAltBlockType L 6 := by
  rintro ⟨-, α, hα, hker, -⟩
  refine card_quot_ne hG2 h1102 h (N := 360) (by norm_num) ?_
  rw [card_quot_of_modO2Surj ⟨hα, hker⟩, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem not_isHatA6Block (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) : ¬ IsHatA6Block L := by
  rintro ⟨-, hH, -⟩
  refine card_quot_ne hG2 h1102 h (N := 1080) (by norm_num) ?_
  rw [card_of_isHat hH, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem not_modO2Surj_SL3_two (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) {α : ↥L →* ↥(StatedSL 3 (ZMod 2))} (hα : IsModO2Surj L α) : False := by
  refine card_quot_ne hG2 h1102 h (N := 168) (by norm_num) ?_
  rw [card_quot_of_modO2Surj hα,
    ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toEquiv,
    card_SL3_oSL3 (m := 1) (by rw [Nat.card_zmod]; norm_num)]
  decide

theorem kindSL3_of_modO2Surj (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) {F : Type} [Field F] [Fintype F] {m : ℕ} (hF : Fintype.card F = 2 ^ m)
    {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) : KindSL3 L (fsuV T I) n ∧ m = n := by
  have hn : 2 ≤ n := h.one_lt
  have hF' : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card, hF]
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have := Fintype.one_lt_card (α := F)
      rw [hF, pow_zero] at this
      exact absurd this (lt_irrefl 1)
    · exact hm
  have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ (3 * m) * oSL3 m := by
    rw [card_quot_of_modO2Surj hα, ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
      card_SL3_oSL3 hF']
  rcases card_quot_cases hG2 h1102 h with ⟨hk, hc'⟩ | ⟨-, hc'⟩ | ⟨-, hc'⟩ <;> rw [hc] at hc'
  · have h1 := eq_of_two_pow_mul_odd (odd_oSL3 hm) (odd_oSL3 (by omega)) hc'
    exact ⟨hk, by omega⟩
  · have h1 := eq_of_two_pow_mul_odd (odd_oSL3 hm) (odd_oSp4 (by omega)) hc'
    rw [h1] at hc'
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) hc'
    obtain ⟨k, rfl, rfl⟩ : ∃ k, m = 4 * k ∧ n = 3 * k := ⟨m - n, by omega, by omega⟩
    exact (not_dvd_oSL3_oSp4 (k := k) (by omega) (h2 ▸ dvd_rfl)).elim
  · have h1 := eq_of_two_pow_mul_odd (odd_oSL3 hm) (odd_oG2 (by omega)) hc'
    rw [h1] at hc'
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) hc'
    obtain rfl : m = 2 * n := by omega
    exact (not_dvd_oSL3_oG2 (n := n) (by omega) (h2 ▸ dvd_rfl)).elim

end CFSG.Quasithin.Vol2.Ch11.SecA
