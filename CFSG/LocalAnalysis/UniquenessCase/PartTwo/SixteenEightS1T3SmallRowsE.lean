module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3CardSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3CardTab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3FixSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutTab
public import CFSG.GroupTheory.PRankBound
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Block

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.false_of_seven_mem_sig_sl (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h3 : 3 ∉ D.sig) (h7 : 7 ∈ D.sig)
    (hL : IsSLn ↥(lBar V₀ V hV L) 6 1 ∨ IsSLn ↥(lBar V₀ V hV L) 7 1) : False := by
  have hsimple_mult : IsSimpleGroup ↥(lBar V₀ V hV L) ∧
      ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k := by
    rcases hL with hL | hL
    · exact s16t3_simple_and_mult hGA hSchur (Or.inl ⟨hL, by norm_num⟩)
    · exact s16t3_simple_and_mult hGA hSchur (Or.inl ⟨hL, by norm_num⟩)
  obtain ⟨hsimple, hmult⟩ := hsimple_mult
  haveI : IsSimpleGroup ↥(lBar V₀ V hV L) := hsimple
  have hKnc : ¬ IsMulCommutative ↥(lBar V₀ V hV L) := by
    intro hc
    exact CFSG.LocalAnalysis.GLTheoremA.SFM12.not_all_commute_of_quasisimple h.quasi
      (fun a b => hc.is_comm.comm a b)
  have hz : Odd (Nat.card (Subgroup.center ↥(lBar V₀ V hV L))) := by
    rw [TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hKnc, Subgroup.card_bot]
    exact odd_one
  have hmultnot : ¬ 7 ∣ Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) := by
    rintro h7dvd
    obtain ⟨k, hk⟩ := hmult
    rw [hk] at h7dvd
    exact absurd (Nat.prime_seven.dvd_of_dvd_pow h7dvd) (by norm_num)
  have hshape : ∃ n : ℕ, (IsSLn ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsSpn ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsOmegaPlus ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsOmegaMinus ↥(lBar V₀ V hV L) n 1 ∧ n < 10) ∨
      (UC22.IsAlt ↥(lBar V₀ V hV L) n ∧ n < 12) := by
    rcases hL with hL | hL
    · exact ⟨6, Or.inl ⟨hL, by norm_num⟩⟩
    · exact ⟨7, Or.inl ⟨hL, by norm_num⟩⟩
  rcases hT.card_irrSet_eq with hIrr3 | hIrr7
  · exact s16t3_not_three_dvd_outer h.quasi hshape (hT.three_dvd_card_outer hIrr3)
  ·
    have hdvd := hT.card_dvd_of_seven hIrr7
    have hval := s16t3_small_shape_valuations h.quasi hshape
    have hnot7_4 : ¬ 7 ^ 4 ∣ Nat.card (Mbar D.M V₀ V hV) := by
      intro h74
      have h74dvd : 7 ^ 4 ∣ 336 * Nat.card ↥(lBar V₀ V hV L) := h74.trans hdvd
      have h73_48 : 7 ^ 3 ∣ 48 * Nat.card ↥(lBar V₀ V hV L) := by
        have h1 : 7 ^ 4 = 7 * 7 ^ 3 := by norm_num
        have h2 : 336 = 7 * 48 := by norm_num
        rw [h2, h1, mul_assoc] at h74dvd
        exact (mul_dvd_mul_iff_left (by norm_num : (7 : ℕ) ≠ 0)).mp h74dvd
      have hcop : Nat.Coprime (7 ^ 3) 48 := by norm_num [Nat.Coprime]
      have h73 : 7 ^ 3 ∣ Nat.card ↥(lBar V₀ V hV L) :=
        (Nat.Coprime.dvd_mul_left hcop).mp h73_48
      exact hval.1 7 Nat.prime_seven (by norm_num) h73
    have hrk : CFSG.Open.pRank 7 (Mbar D.M V₀ V hV) ≤ 3 :=
      CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (p := 7) (k := 3) Nat.prime_seven hnot7_4
    have hker : 7 ∣ Nat.card (F11.CTilde D.M V₀ V) :=
      s16g_dvd_card_cTilde D h.std h.setting h7 hrk
    have hfix : ∀ x : Vtil V₀ V hV, x ≠ 1 →
        ∃ y ∈ lBar V₀ V hV L, orderOf y = 7 ∧ y x = x :=
      hT.exists_fix_seven_sl hL
    exact s16g_false_of_fix_lBar D h.std h.setting h.quasi hz Nat.prime_seven (by norm_num) h7
      hmultnot hker hfix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
