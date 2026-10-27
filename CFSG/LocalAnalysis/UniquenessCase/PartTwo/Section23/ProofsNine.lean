module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2TransferSL3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem nonempty_bar2_mulEquiv_H_of_isSLn {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (hK : KOrdNatural) {n j : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) n) (hS3 : KSchurSL3)
    (hshape : IsSLn (c.H hV) 3 j) (hj : 3 ≤ j) :
    Nonempty (Bar2 c.L ≃* ↥(c.H hV)) :=
  (comap_pCore_eq_of_pCore_eq_bot_of_isSLn (c.phiL hV) (c.phiL_surjective hV)
    (c.commutator_L_eq_top) (c.phiL_ker_commutator_mem_pCore hV hK hnat) hS3 hshape hj
    (hK.1 hnat)).2

theorem isL2_quotientPCore_of_isL2 {X : Type} [Group X] {j : ℕ} (h : IsL2 X j)
    (hbot : CFSG.pCore 2 X = ⊥) : IsL2 (X ⧸ CFSG.pCore 2 X) j :=
  CFSG.Blueprint.LieModel.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm h

theorem isL2Square_quotientPCore_of_isL2Square {X : Type} [Group X] {j : ℕ}
    (h : IsL2Square X j) (hbot : CFSG.pCore 2 X = ⊥) :
    IsL2Square (X ⧸ CFSG.pCore 2 X) j :=
  IsL2Square.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).symm h

private theorem four_shapes_of_isNaturalClassicalModule {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) {hV : IsElemAbelian 2 c.V} {n : ℕ}
    (hnat : IsNaturalClassicalModule (c.H hV) n)
    (h1 : ¬ ((IsSp4 ↥(c.H hV) n ∧ NatSpn (c.H hV) ⊤ ⊥ 4 n) ∨
      (∃ a : ℕ, n = 2 * a ∧ IsSUn ↥(c.H hV) 4 a ∧ NatSUn (c.H hV) ⊤ ⊥ 4 a) ∨
      (IsOmegaMinus ↥(c.H hV) 6 n ∧ NatOmegaMinus (c.H hV) ⊤ ⊥ 6 n)))
    (h2 : ¬ (IsOmegaPlus ↥(c.H hV) 6 n ∧ NatOmegaPlus (c.H hV) ⊤ ⊥ 6 n))
    (h3 : ¬ ((IsSLn ↥(c.H hV) 4 n ∧ CFSG.Quasithin.BinaryNaturalSL (c.H hV) ⊤ ⊥ 4 n) ∨
      (IsSpn ↥(c.H hV) 6 n ∧ NatSpn (c.H hV) ⊤ ⊥ 6 n) ∨
      (IsOmega8m ↥(c.H hV) n ∧ NatOmegaMinus (c.H hV) ⊤ ⊥ 8 n))) :
    IsL2 ↥(c.H hV) n ∨ IsOmegaMinus ↥(c.H hV) 4 n ∨ IsOmegaPlus ↥(c.H hV) 4 n ∨
      IsSLn ↥(c.H hV) 3 n := by
  rcases hnat with ⟨hL2, hBin2⟩ | ⟨hMinus4, hNatMinus4⟩ | ⟨hPlus4, hNatPlus4⟩ |
    ⟨hSp4, hNatSp4⟩ | ⟨hSL3, hBin3⟩ | ⟨a, ha, hSU4, hNatSU4⟩ | ⟨hOm6, hNatOm6⟩ |
    ⟨hSL4, hBin4⟩ | ⟨hOp6, hNatOp6⟩ | ⟨hSp6, hNatSp6⟩ | ⟨hO8, hNatO8⟩
  · exact Or.inl hL2
  · exact Or.inr (Or.inl hMinus4)
  · exact Or.inr (Or.inr (Or.inl hPlus4))
  · exact (h1 (Or.inl ⟨hSp4, hNatSp4⟩)).elim
  · exact Or.inr (Or.inr (Or.inr hSL3))
  · exact (h1 (Or.inr (Or.inl ⟨a, ha, hSU4, hNatSU4⟩))).elim
  · exact (h1 (Or.inr (Or.inr ⟨hOm6, hNatOm6⟩))).elim
  · exact (h3 (Or.inl ⟨hSL4, hBin4⟩)).elim
  · exact (h2 ⟨hOp6, hNatOp6⟩).elim
  · exact (h3 (Or.inr (Or.inl ⟨hSp6, hNatSp6⟩))).elim
  · exact (h3 (Or.inr (Or.inr ⟨hO8, hNatO8⟩))).elim

theorem s23_9_2_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (h4 : S23_4 D Ch)
    (hline : S23_5_line D Ch) (hKN : KNshape) (hK : KOrdNatural) (hS : KSchurL2)
    (hS3 : KSchurSL3) (hN1 : S23_9_NotSp4SU4O6m D Ch) (hN2 : S23_9_NotO6p D Ch)
    (hN3 : S23_9_NotLarge D Ch) : S23_9_2 D Ch := by
  intro h1930 c
  let n : ℕ := CFSG.Open.pRank 2 D.Z
  have hn3c : 3 ≤ c.n := uc22p20g_hn3_of hE D Ch h207 h1930 c.toCtx23.toCtx21
  rcases hline h1930 c with hL020 | ⟨hLL0, hMinus, hL2two, hPi⟩ |
    ⟨hLL0, hPlusSq, hCyc, hEcyc⟩
  · have hcn : c.n = CFSG.Open.pRank 2 D.Z := hKN G c.L0 c.n n c.hn (Or.inl hL020)
    have hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z := hcn ▸ hn3c
    have hn2 : 2 ≤ n := le_trans (by norm_num) hn3
    obtain ⟨hV, hnat⟩ := Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c
    have hnat0 := hnat
    have hbotH : CFSG.pCore 2 (c.H hV) = ⊥ := hK.1 hnat
    have h1 := hN1 h1930 c hn3 hV
    have h2' := hN2 h1930 c hn3 hV
    have h3' := hN3 h1930 c hn3 hV
    rcases four_shapes_of_isNaturalClassicalModule c hnat h1 h2' h3' with
      hL2 | hMinus4 | hPlus4 | hSL3
    · have hshape : IsL2 (c.H hV ⧸ CFSG.pCore 2 (c.H hV)) n :=
        isL2_quotientPCore_of_isL2 hL2 hbotH
      obtain ⟨e⟩ := c.nonempty_bar2_mulEquiv hV hK hnat0 hS (Or.inl hshape)
      exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hL2)
    · have hn1 : 1 ≤ n := le_trans (by norm_num) hn2
      have hshape : IsL2 (c.H hV ⧸ CFSG.pCore 2 (c.H hV)) (2 * n) :=
        isL2_quotientPCore_of_isL2
          (isL2_two_mul_of_isOmegaMinus_four hn1 hMinus4) hbotH
      obtain ⟨e⟩ := c.nonempty_bar2_mulEquiv hV hK hnat0 hS (Or.inl hshape)
      exact Or.inr (Or.inr (Or.inl (IsOmegaMinus.of_mulEquiv e.symm hMinus4)))
    · have hsq : IsL2Square ↥(c.H hV) n :=
        (isOmegaPlus_four_iff_isL2Square hn2).mp hPlus4
      have hshape : IsL2Square (c.H hV ⧸ CFSG.pCore 2 (c.H hV)) n :=
        isL2Square_quotientPCore_of_isL2Square hsq hbotH
      obtain ⟨e⟩ := c.nonempty_bar2_mulEquiv hV hK hnat0 hS (Or.inr hshape)
      exact Or.inr (Or.inl (IsOmegaPlus.of_mulEquiv e.symm hPlus4))
    · obtain ⟨e⟩ := nonempty_bar2_mulEquiv_H_of_isSLn c hV hK hnat0 hS3 hSL3 hn3
      exact Or.inr (Or.inr (Or.inr (IsSLn.of_mulEquiv e.symm hSL3)))
  · exact Or.inr (Or.inr (Or.inl hMinus))
  · have hcn : c.n = CFSG.Open.pRank 2 D.Z := hKN G c.L0 c.n n c.hn (Or.inr hPlusSq)
    have hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z := hcn ▸ hn3c
    have hplus : IsOmegaPlus (Bar2 c.L) 4 n := by
      rw [hLL0]
      exact (isOmegaPlus_four_iff_isL2Square (le_trans (by norm_num) hn3)).2 hPlusSq
    exact Or.inr (Or.inl hplus)

theorem s23_9_1_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h52 : S23_5_2 D Ch) (hPS : S23_9_PointStab D Ch) (hB23 : S23_9_B23 D Ch)
    (hN1 : S23_9_NotSp4SU4O6m D Ch) (hN2 : S23_9_NotO6p D Ch) : S23_9_1 D Ch := by
  intro h1930 c
  let n : ℕ := CFSG.Open.pRank 2 D.Z
  have hn3c : 3 ≤ c.n := uc22p20g_hn3_of hE D Ch h207 h1930 c.toCtx23.toCtx21
  rcases h52 h1930 c with hcn | ⟨hLL0, hMinus, hcn2⟩
  · have hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z := hcn ▸ hn3c
    rcases hB23 h1930 c hn3 with hbot | hcal | ⟨hOmega, -⟩ | ⟨hSU, -⟩
    · exact Or.inl hbot
    · exact Or.inr hcal
    · obtain ⟨hV, hplus, hnatplus⟩ := hOmega
      exact (hN2 h1930 c hn3 hV ⟨hplus, hnatplus⟩).elim
    · obtain ⟨hV, a, ha, hsu, hnatsu⟩ := hSU
      exact (hN1 h1930 c hn3 hV (Or.inr (Or.inl ⟨a, ha, hsu, hnatsu⟩))).elim
  · exact Or.inl ((hPS h1930 c).2.2 n hMinus)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
