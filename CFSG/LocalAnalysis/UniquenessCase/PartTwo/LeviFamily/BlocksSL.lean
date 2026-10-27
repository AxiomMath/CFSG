module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.CensusDefs
import CFSG.Quasithin.Vol2.Ch11L2Q5cNot3
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Index
import CFSG.LargeExtraspecial.A2ModSLModel
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Arith
import CFSG.RankThree.PartOne.F106.ConvOrdBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem range_toGL_eq_bot_iff (m : ℕ) :
    (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range = ⊥ ↔ m ≤ 1 := by
  set S : Subgroup (GL (Fin m) K) :=
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range
  have e : Matrix.SpecialLinearGroup (Fin m) K ≃* ↥S :=
    CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := K) m
  constructor
  · intro hbot
    by_contra hm
    rw [not_le] at hm
    have hcard := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := m)
      (by omega : 1 ≤ m)
    have hgt : 1 < Nat.card (Matrix.SpecialLinearGroup (Fin m) K) := by
      rw [hcard]
      have hq2 : 2 ≤ Nat.card K := by
        have := Finite.one_lt_card (α := K)
        omega
      have h2mem : 2 ∈ Finset.Icc 2 m := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
      have hfac : 3 ≤ Nat.card K ^ 2 - 1 := by
        have h4 : 4 ≤ Nat.card K ^ 2 := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq2 2
        omega
      have hprod : 3 ≤ ∏ j ∈ Finset.Icc 2 m, (Nat.card K ^ j - 1) := by
        rw [← Finset.prod_erase_mul (s := Finset.Icc 2 m)
          (f := fun j => Nat.card K ^ j - 1) h2mem]
        have hge1 : 1 ≤ ∏ j ∈ (Finset.Icc 2 m).erase 2, (Nat.card K ^ j - 1) := by
          refine Finset.one_le_prod ?_
          intro j hj
          rw [Finset.mem_erase, Finset.mem_Icc] at hj
          have hj2 : 2 ≤ j := by omega
          have h4j : 4 ≤ Nat.card K ^ j := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq2 2
              _ ≤ Nat.card K ^ j := Nat.pow_le_pow_right (by omega) hj2
          omega
        simpa using Nat.mul_le_mul hge1 hfac
      have hqa : 1 ≤ Nat.card K ^ (m * (m - 1) / 2) :=
        Nat.one_le_pow _ _ (by have := Finite.one_lt_card (α := K); omega)
      have := Nat.mul_le_mul hqa hprod
      omega
    have h1 : Nat.card ↥S = 1 := by rw [hbot, Subgroup.card_bot]
    have h2 : Nat.card (Matrix.SpecialLinearGroup (Fin m) K) = Nat.card ↥S :=
      Nat.card_congr e.toEquiv
    omega
  · intro hm
    have hm2 : m < 2 := by omega
    have hsub : Subsingleton (Matrix.SpecialLinearGroup (Fin m) K) :=
      CFSG.AGLEmbedding.LeviBlock.subsingleton_specialLinear_of_lt_two (K := K) hm2
    have hsubS : Subsingleton ↥S := @Equiv.subsingleton _ _ e.symm.toEquiv hsub
    exact @Subgroup.eq_bot_of_subsingleton _ _ S hsubS

theorem range_toGL_eq_bot_or_isLeviBlock (m : ℕ) :
    (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range = ⊥ ∨
      IsLeviBlock ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range := by
  set S : Subgroup (GL (Fin m) K) :=
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range
  have e : Matrix.SpecialLinearGroup (Fin m) K ≃* ↥S :=
    CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := K) m
  rcases CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.range_toGL_cases (K := K) m with
    hbot | ⟨hK2, hm2, -⟩ | ⟨hq, hodd⟩
  · exact Or.inl hbot
  · right
    subst hm2
    obtain ⟨f⟩ := CFSG.StandardType.RCSPSL.nonempty_sl2_equiv_perm (F := K) hK2
    exact Or.inl ⟨(CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := K) 2).symm.trans f⟩
  · right
    refine Or.inr (Or.inr ⟨hq, hodd, ?_⟩)
    have hqSL : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin m) K) :=
      CFSG.Open.IsQuasisimple.of_mulEquiv e hq
    have hm2 : 2 ≤ m :=
      CFSG.AGLEmbedding.LeviBlock.two_le_of_isQuasisimple_specialLinear hqSL
    rw [← Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := m) (by omega)]
    obtain ⟨r, hr0, hcard⟩ :=
      CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.card_eq_two_pow_of_charP_two (K := K)
    have hdvd : 2 ∣ Nat.card K ^ (m * (m - 1) / 2) := by
      rw [hcard, ← pow_mul]
      have ha : m * (m - 1) / 2 ≠ 0 := by
        have h2le : 2 ≤ m * (m - 1) := by
          calc 2 = 2 * 1 := by norm_num
            _ ≤ m * (m - 1) := Nat.mul_le_mul hm2 (by omega)
        have hdiv : 0 < m * (m - 1) / 2 := Nat.div_pos h2le (by norm_num)
        omega
      exact dvd_pow_self 2 (Nat.mul_ne_zero (by omega) ha)
    exact dvd_mul_of_dvd_left hdvd _

theorem range_toGL_eq_bot_or_isQuasisimple (hK : Nat.card K ≠ 2) (m : ℕ) :
    (Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range = ⊥ ∨
      CFSG.Open.IsQuasisimple ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range := by
  rcases CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.range_toGL_cases (K := K) m with
    hbot | ⟨hK2, -, -⟩ | ⟨hq, -⟩
  · exact Or.inl hbot
  · exact absurd hK2 hK
  · exact Or.inr hq

omit [CharP K 2] in
private theorem card_quotient_center_range_toGL (hK : Nat.card K = 2) (m : ℕ) :
    Nat.card (↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range ⧸
      Subgroup.center ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range) =
    Nat.card (Matrix.SpecialLinearGroup (Fin m) K) := by
  set S : Subgroup (GL (Fin m) K) :=
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range
  have e : Matrix.SpecialLinearGroup (Fin m) K ≃* ↥S :=
    CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := K) m
  have hZ : Subgroup.center ↥S = ⊥ := by
    have hZSL : Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K) = ⊥ :=
      CFSG.LargeExtraspecial.A2Mod.sl_center_eq_bot_of_card_two (n := m) hK
    have hc := Subgroup.centerCongr e
    have hsubSL : Subsingleton ↥(Subgroup.center (Matrix.SpecialLinearGroup (Fin m) K)) := by
      rw [hZSL]
      infer_instance
    have hsubS : Subsingleton ↥(Subgroup.center ↥S) :=
      @Equiv.subsingleton _ _ hc.symm.toEquiv hsubSL
    exact @Subgroup.eq_bot_of_subsingleton _ _ _ hsubS
  rw [hZ]
  calc Nat.card (↥S ⧸ ⊥) = Nat.card ↥S :=
        Nat.card_congr QuotientGroup.quotientBot.toEquiv
    _ = Nat.card (Matrix.SpecialLinearGroup (Fin m) K) :=
        (Nat.card_congr e.toEquiv).symm

private theorem two_pow_mul_odd_eq_of_card_specialLinear {m n : ℕ} (hn : 1 ≤ n)
    (heq : 2 ^ n * ((2 ^ n) ^ 2 - 1) =
      2 ^ (m * (m - 1) / 2) * ∏ j ∈ Finset.Icc 2 m, (2 ^ j - 1)) :
    n = m * (m - 1) / 2 ∧
      (2 ^ n) ^ 2 - 1 = ∏ j ∈ Finset.Icc 2 m, (2 ^ j - 1) := by
  have hPodd : Odd (∏ j ∈ Finset.Icc 2 m, (2 ^ j - 1)) :=
    Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun j hj =>
      CFSG.GroupTheory.SuzukiTwoGroup.odd_two_pow_sub_one
        (by have := (Finset.mem_Icc.1 hj).1; omega)
  have hBodd : Odd ((2 ^ n) ^ 2 - 1) := by
    have heven : Even ((2 ^ n) ^ 2) := by
      rw [← pow_mul, Nat.mul_comm]
      exact even_two.pow_of_ne_zero (by omega : 2 * n ≠ 0)
    have hpos : 1 ≤ (2 ^ n) ^ 2 := by
      have := Nat.one_le_pow 2 (2 ^ n) (by positivity)
      simpa using this
    exact Nat.Even.sub_odd hpos heven odd_one
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23.knl_two_pow_mul_odd_inj
    hBodd hPodd heq

private theorem prod_two_pow_sub_one_lt_sq_sub_one {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hna : n = m * (m - 1) / 2) :
    ∏ j ∈ Finset.Icc 2 m, (2 ^ j - 1) < (2 ^ n) ^ 2 - 1 := by
  have hS_eq : 2 * (∑ j ∈ Finset.Icc 2 m, j) = (m - 1) * (m + 2) := by
    have h := CFSG.RankThree.PartOne.F106.two_mul_sum_Icc_two (m - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ m), show m - 1 + 3 = m + 2 by omega] at h
    exact h
  have h2n : 2 * (m * (m - 1) / 2) = m * (m - 1) := by
    have heven : Even (m * (m - 1)) := by
      have h := Nat.even_mul_succ_self (m - 1)
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
      simpa [Nat.mul_comm] using h
    exact Nat.mul_div_cancel' heven.two_dvd
  have hP_le : ∏ j ∈ Finset.Icc 2 m, (2 ^ j - 1) ≤
      2 ^ (∑ j ∈ Finset.Icc 2 m, j) :=
    CFSG.RankThree.PartOne.F106.prod_sub_one_le 2 (Finset.Icc 2 m) id
  have hSle : (∑ j ∈ Finset.Icc 2 m, j) ≤ 2 * n - 1 := by
    have hmain : 2 * (∑ j ∈ Finset.Icc 2 m, j) ≤ 2 * (2 * n - 1) := by
      rw [hS_eq, hna, h2n]
      have h5 : (m - 1) * (m + 2) + 2 ≤ 2 * (m * (m - 1)) := by
        have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega : 1 ≤ m)
        have hm3' : m - 3 + 3 = m := Nat.sub_add_cancel (by omega : 3 ≤ m)
        have hnonneg : 0 ≤ m * (m - 3) := Nat.zero_le _
        nlinarith
      simpa [Nat.mul_sub_left_distrib] using Nat.le_sub_of_add_le h5
    omega
  have hpow : 2 ^ (∑ j ∈ Finset.Icc 2 m, j) ≤ 2 ^ (2 * n - 1) :=
    Nat.pow_le_pow_right (by norm_num) hSle
  have hB_gt : 2 ^ (2 * n - 1) < (2 ^ n) ^ 2 - 1 := by
    have hpow2 : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [hpow2]
    have hsplit : 2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
      conv_lhs => rw [show 2 * n = (2 * n - 1) + 1 by omega]
      rw [pow_succ']
    rw [hsplit]
    have hx : 1 < 2 ^ (2 * n - 1) :=
      Nat.one_lt_two_pow (by omega)
    omega
  exact lt_of_le_of_lt (le_trans hP_le hpow) hB_gt

private theorem card_specialLinear_two_ne_l2_order {m n : ℕ} (hm : 1 ≤ m) (hn : 3 ≤ n) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠
      2 ^ (m * (m - 1) / 2) * ∏ j ∈ Finset.Icc 2 m, (2 ^ j - 1) := by
  intro heq
  obtain ⟨hna, hBP⟩ := two_pow_mul_odd_eq_of_card_specialLinear (by omega : 1 ≤ n) heq
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  · interval_cases m
    · omega
    · have : n = 1 := by simpa using hna
      omega
  · have hlt := prod_two_pow_sub_one_lt_sq_sub_one hm3 hn hna
    omega

omit [CharP K 2] in
theorem not_isL2_range_toGL (hK : Nat.card K = 2) (m : ℕ)
    (hq : CFSG.Open.IsQuasisimple ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range) {n : ℕ} (hn : 3 ≤ n) :
    ¬ IsL2 (↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range ⧸
      center ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range) n := by
  set S : Subgroup (GL (Fin m) K) :=
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range
  intro hL2
  have hTcard : Nat.card (↥S ⧸ Subgroup.center ↥S) =
      Nat.card (Matrix.SpecialLinearGroup (Fin m) K) :=
    card_quotient_center_range_toGL (K := K) hK m
  have hcardL2 : Nat.card (↥S ⧸ Subgroup.center ↥S) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hL2)
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · have hSL0 : Nat.card (Matrix.SpecialLinearGroup (Fin 0) K) = 1 := by
      have hsub : Subsingleton (Matrix.SpecialLinearGroup (Fin 0) K) :=
        CFSG.AGLEmbedding.LeviBlock.subsingleton_specialLinear_of_lt_two (K := K) (by omega)
      exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rw [hTcard, hSL0] at hcardL2
    have hgt : 1 < 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      have h2n : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega : 1 ≤ n)
      have hsq : 4 ≤ (2 ^ n) ^ 2 := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2n 2
      have h1' : 1 < 2 ^ n := by omega
      have h2' : 1 < (2 ^ n) ^ 2 - 1 := by omega
      nlinarith
    exact hgt.ne' hcardL2.symm
  · have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin m) K) =
        2 ^ (m * (m - 1) / 2) * ∏ j ∈ Finset.Icc 2 m, (2 ^ j - 1) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := K) (n := m) hmpos,
        hK]
    exact card_specialLinear_two_ne_l2_order hmpos hn (by rw [← hcardL2, hTcard, hcardSL])

omit [CharP K 2] in
theorem three_dvd_card_quotient_center_range_toGL {m : ℕ} (hm : 2 ≤ m) :
    3 ∣ Nat.card (↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range ⧸
      center ↥(Matrix.SpecialLinearGroup.toGL :
        Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range) := by
  set S : Subgroup (GL (Fin m) K) :=
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin m) K →* GL (Fin m) K).range
  have e : Matrix.SpecialLinearGroup (Fin m) K ≃* ↥S :=
    CFSG.AGLEmbedding.LeviBlock.slEquivToGLRange (K := K) m
  rw [Nat.card_congr (QuotientGroup.congr _ _
    e.symm (CFSG.AGLEmbedding.LeviBlock.map_center_mulEquiv e.symm)).toEquiv]
  exact CFSG.Quasithin.Vol2.Ch11.SecB.three_dvd_card_psl (K := K) hm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily
