module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2TransferSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.EmptyFaithful.A38cOrders
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem not_isL2_of_isSLn_three {X : Type} [Group X] {a b : ℕ}
    (hSL : IsSLn X 3 a) : ¬ IsL2 X b := by
  intro hL
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSL
  letI := hKf
  letI := hKfin
  have ha1 : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    rw [hKcard, ha0, pow_zero] at h2
    exact (lt_irrefl 1) h2
  have hb1 : 1 ≤ b := hL.admissible.2.1
  have hSLcard : Nat.card X =
      2 ^ (3 * a) * ((2 ^ (3 * a) - 1) * (2 ^ (2 * a) - 1)) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, hKcard]
    have h3 : (2 ^ a) ^ 3 = 2 ^ (3 * a) := by rw [← pow_mul]; ring
    have h2 : (2 ^ a) ^ 2 = 2 ^ (2 * a) := by rw [← pow_mul]; ring
    rw [h3, h2]
    congr 1
    exact mul_comm _ _
  have hLcard : Nat.card X = 2 ^ b * (4 ^ b - 1) := by
    have hSC : StatedClassicalModel X .PSL 2 2 b :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hL
    rw [CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hSC]
    have h4 : (2 ^ b) ^ 2 = 4 ^ b := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [h4]
  exact CFSG.Quasithin.card_sl_two_ne_card_sl_three hb1 ha1 (hLcard.symm.trans hSLcard)

private theorem sl3Odd_lt_l2SquareOdd {a : ℕ} (ha : 1 ≤ a) :
    (2 ^ (2 * a) - 1) * (2 ^ (3 * a) - 1) < (2 ^ (3 * a) - 1) ^ 2 := by
  have hlt : 2 ^ (2 * a) - 1 < 2 ^ (3 * a) - 1 := by
    have h : 2 ^ (2 * a) < 2 ^ (3 * a) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h2a : 0 < 2 ^ (2 * a) := by positivity
    omega
  have hy : 0 < 2 ^ (3 * a) - 1 := by
    have h : 1 < 2 ^ (3 * a) := Nat.one_lt_two_pow (by omega)
    omega
  calc (2 ^ (2 * a) - 1) * (2 ^ (3 * a) - 1)
      < (2 ^ (3 * a) - 1) * (2 ^ (3 * a) - 1) :=
        Nat.mul_lt_mul_of_pos_right hlt hy
    _ = (2 ^ (3 * a) - 1) ^ 2 := by ring

theorem not_isL2Square_of_isSLn_three {X : Type} [Group X] {a b : ℕ}
    (hSL : IsSLn X 3 a) : ¬ IsL2Square X b := by
  intro hSQ
  obtain ⟨A, B, hAg, hBg, ⟨e⟩, hA, hB⟩ := hSQ
  letI : Group A := hAg
  letI : Group B := hBg
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eSL⟩⟩ := hSL
  letI := hKf
  letI := hKfin
  have ha1 : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    have h2 : 1 < Nat.card K := Finite.one_lt_card
    rw [hKcard, ha0, pow_zero] at h2
    exact (lt_irrefl 1) h2
  have hb1 : 1 ≤ b := hA.admissible.2.1
  have hSLcard : Nat.card X =
      2 ^ (3 * a) * ((2 ^ (2 * a) - 1) * (2 ^ (3 * a) - 1)) := by
    rw [Nat.card_congr eSL.toEquiv, CFSG.Open.StatedAPI.card_statedSL_three, hKcard]
    have h3 : (2 ^ a) ^ 3 = 2 ^ (3 * a) := by rw [← pow_mul]; ring
    have h2 : (2 ^ a) ^ 2 = 2 ^ (2 * a) := by rw [← pow_mul]; ring
    rw [h3, h2]
  have hAcard : Nat.card A = 2 ^ b * ((2 ^ b) ^ 2 - 1) := by
    have hSC : StatedClassicalModel A .PSL 2 2 b :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA
    exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hSC
  have hBcard : Nat.card B = 2 ^ b * ((2 ^ b) ^ 2 - 1) := by
    have hSC : StatedClassicalModel B .PSL 2 2 b :=
      CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB
    exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hSC
  have hSQcard : Nat.card X = 2 ^ (2 * b) * ((2 ^ (2 * b) - 1) ^ 2) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, hAcard, hBcard]
    have hp : 2 ^ b * 2 ^ b = 2 ^ (2 * b) := by rw [← pow_add]; ring
    have hsq : (2 ^ b) ^ 2 = 2 ^ (2 * b) := by rw [← pow_mul]; ring
    calc 2 ^ b * ((2 ^ b) ^ 2 - 1) * (2 ^ b * ((2 ^ b) ^ 2 - 1))
        = (2 ^ b * 2 ^ b) * (((2 ^ b) ^ 2 - 1) * ((2 ^ b) ^ 2 - 1)) := by ring
      _ = 2 ^ (2 * b) * ((2 ^ (2 * b) - 1) ^ 2) := by rw [hp, hsq]; ring
  have hRodd : Odd ((2 ^ (2 * a) - 1) * (2 ^ (3 * a) - 1)) := by
    refine Odd.mul ?_ ?_
    · exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
    · exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
  have hSodd : Odd ((2 ^ (2 * b) - 1) ^ 2) :=
    (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)).pow
  have hb : 3 * a = 2 * b :=
    CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hRodd hSodd
      (hSLcard.symm.trans hSQcard)
  have hRS : (2 ^ (2 * a) - 1) * (2 ^ (3 * a) - 1) = (2 ^ (2 * b) - 1) ^ 2 := by
    have h := hSLcard.symm.trans hSQcard
    rw [hb] at h
    have h' : (2 ^ (2 * a) - 1) * (2 ^ (2 * b) - 1) = (2 ^ (2 * b) - 1) ^ 2 :=
      Nat.mul_left_cancel (show 0 < 2 ^ (2 * b) by positivity) h
    simpa [hb] using h'
  rw [← hb] at hRS
  exact (ne_of_lt (sl3Odd_lt_l2SquareOdd ha1)) hRS

private theorem sl3Line_aux {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h1930 : H1930 D) (hK : KOrdNatural) (hS : KSchurL2) (hS3 : KSchurSL3)
    (hSL3 : IsSLn (Bar2 c.L) 3 (CFSG.Open.pRank 2 D.Z))
    (hN1 : S23_9_NotSp4SU4O6m D Ch) (hN2 : S23_9_NotO6p D Ch)
    (hN3 : S23_9_NotLarge D Ch) {hV : IsElemAbelian 2 c.V}
    (hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) :
    IsSLn ↥(c.H hV) 3 (CFSG.Open.pRank 2 D.Z) ∧
      BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 (CFSG.Open.pRank 2 D.Z) ∧
        (c.phiL hV).ker = CFSG.pCore 2 ↥c.L := by
  have hnat0 := hnat
  have hbotH : CFSG.pCore 2 ↥(c.H hV) = ⊥ := hK.1 hnat0
  let e0 : (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV)) ≃* ↥(c.H hV) :=
    (QuotientGroup.quotientMulEquivOfEq hbotH).trans QuotientGroup.quotientBot
  have hm1 : 1 ≤ CFSG.Open.pRank 2 D.Z := by omega
  have hm2 : 2 ≤ CFSG.Open.pRank 2 D.Z := by omega
  rcases hnat with ⟨hL2, -⟩ | ⟨hMinus4, -⟩ | ⟨hPlus4, -⟩ | ⟨hSp4, hNatSp4⟩ |
    ⟨hSL3H, hBin3⟩ | ⟨a, ha, hSU4, hNatSU4⟩ | ⟨hOm6, hNatOm6⟩ | ⟨hSL4, hBin4⟩ |
    ⟨hOp6, hNatOp6⟩ | ⟨hSp6, hNatSp6⟩ | ⟨hO8, hNatO8⟩
  · have hshape : IsL2 (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV))
        (CFSG.Open.pRank 2 D.Z) :=
      CFSG.Blueprint.LieModel.of_mulEquiv e0.symm hL2
    obtain ⟨e⟩ := c.nonempty_bar2_mulEquiv hV hK hnat0 hS (Or.inl hshape)
    exact (not_isL2_of_isSLn_three hSL3
      (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2)).elim
  · have hshape : IsL2 (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV))
        (2 * CFSG.Open.pRank 2 D.Z) :=
      CFSG.Blueprint.LieModel.of_mulEquiv e0.symm
        (isL2_two_mul_of_isOmegaMinus_four hm1 hMinus4)
    obtain ⟨e⟩ := c.nonempty_bar2_mulEquiv hV hK hnat0 hS (Or.inl hshape)
    exact (not_isL2_of_isSLn_three hSL3
      (CFSG.Blueprint.LieModel.of_mulEquiv e.symm
        (isL2_two_mul_of_isOmegaMinus_four hm1 hMinus4))).elim
  · have hsq : IsL2Square ↥(c.H hV) (CFSG.Open.pRank 2 D.Z) :=
      (isOmegaPlus_four_iff_isL2Square hm2).mp hPlus4
    have hshape : IsL2Square (↥(c.H hV) ⧸ CFSG.pCore 2 ↥(c.H hV))
        (CFSG.Open.pRank 2 D.Z) := IsL2Square.of_mulEquiv e0.symm hsq
    obtain ⟨e⟩ := c.nonempty_bar2_mulEquiv hV hK hnat0 hS (Or.inr hshape)
    exact (not_isL2Square_of_isSLn_three hSL3
      (IsL2Square.of_mulEquiv e.symm hsq)).elim
  · exact (hN1 h1930 c hn3 hV (Or.inl ⟨hSp4, hNatSp4⟩)).elim
  · refine ⟨hSL3H, hBin3, ?_⟩
    exact (comap_pCore_eq_of_pCore_eq_bot_of_isSLn (c.phiL hV) (c.phiL_surjective hV)
      (c.commutator_L_eq_top) (c.phiL_ker_commutator_mem_pCore hV hK hnat0) hS3
      hSL3H hn3 hbotH).1
  · exact (hN1 h1930 c hn3 hV (Or.inr (Or.inl ⟨a, ha, hSU4, hNatSU4⟩))).elim
  · exact (hN1 h1930 c hn3 hV (Or.inr (Or.inr ⟨hOm6, hNatOm6⟩))).elim
  · exact (hN3 h1930 c hn3 hV (Or.inl ⟨hSL4, hBin4⟩)).elim
  · exact (hN2 h1930 c hn3 hV ⟨hOp6, hNatOp6⟩).elim
  · exact (hN3 h1930 c hn3 hV (Or.inr (Or.inl ⟨hSp6, hNatSp6⟩))).elim
  · exact (hN3 h1930 c hn3 hV (Or.inr (Or.inr ⟨hO8, hNatO8⟩))).elim

theorem Ctx2311.sl3Line_of {D : Data G} {Ch : Choice2011 G} (c : Ctx2311 D Ch)
    (h1930 : H1930 D) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (hline : S23_5_line D Ch) (hKN : KNshape) (hK : KOrdNatural) (hS : KSchurL2)
    (hS3 : KSchurSL3) (hN1 : S23_9_NotSp4SU4O6m D Ch) (hN2 : S23_9_NotO6p D Ch)
    (hN3 : S23_9_NotLarge D Ch) :
    let m := CFSG.Open.pRank 2 D.Z
    3 ≤ m ∧ ∃ hV : IsElemAbelian 2 c.V, IsSLn ↥(c.H hV) 3 m ∧
      BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 m ∧ (c.phiL hV).ker = CFSG.pCore 2 ↥c.L := by
  let m := CFSG.Open.pRank 2 D.Z
  change 3 ≤ m ∧ ∃ hV : IsElemAbelian 2 c.V, IsSLn ↥(c.H hV) 3 m ∧
    BinaryNaturalSL (c.H hV) ⊤ ⊥ 3 m ∧ (c.phiL hV).ker = CFSG.pCore 2 ↥c.L
  have hn3c : 3 ≤ c.n := uc22p20g_hn3_of hE D Ch h207 h1930 c.toCtx23.toCtx21
  rcases hline h1930 c.toCtx23L with hline1 | ⟨hLL0, -, hL2two, -⟩ | ⟨hLL0, hPlusSq, -, -⟩
  · have hcn : c.n = m := hKN G c.L0 c.n m c.hn (Or.inl hline1)
    have hn3 : 3 ≤ m := hcn ▸ hn3c
    obtain ⟨hV, hnat⟩ :=
      Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c.toCtx23L
    exact ⟨hn3, hV, sl3Line_aux c.toCtx23L h1930 hK hS hS3 c.hSL3 hN1 hN2 hN3 hn3 hnat⟩
  · have hL2 : IsL2 (Bar2 c.L) (2 * m) := by
      change IsL2 (Bar2 c.L) (2 * CFSG.Open.pRank 2 D.Z)
      rw [hLL0]
      exact hL2two
    exact (not_isL2_of_isSLn_three c.hSL3 hL2).elim
  · have hcn : c.n = m := hKN G c.L0 c.n m c.hn (Or.inr hPlusSq)
    have hn3 : 3 ≤ m := hcn ▸ hn3c
    obtain ⟨hV, hnat⟩ :=
      Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c.toCtx23L
    exact ⟨hn3, hV, sl3Line_aux c.toCtx23L h1930 hK hS hS3 c.hSL3 hN1 hN2 hN3 hn3 hnat⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
