module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneLbar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOne
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneONan
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneL227Final
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneLieAut
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K5Alt
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

variable {G : Type} [Group G] [Finite G]

structure KInputs811 : Prop where
  k1 : K1
  k2 : K2
  k3 : K3Exp
  k3Out : K3Out
  k4a : K4a
  k4b : K4b
  k5J3 : K5J3
  k5ONan : K5ONan
  k5U42 : K5U42
  k5L227 : K5L227
  k6a : K6a
  k6b : K6b
  k6c : K6c
  k6d : K6dL4
  k6r : K6r
  k6L4 : K6L4
  k6Z : K6ZL4
  k7 : K7

@[expose] def Section8L4Residual (c : Counterexample4 G) : Prop :=
  ∀ (_ : Case811Sylow c) (r : ℕ), IsLie811 c.Lbar .l4 r 1 →
    (∀ p ∈ CFSG.Open.uniqueFourSigma c.S.M, p = r) → r ∈ CFSG.Open.uniqueFourSigma c.S.M →
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M r →
    CFSG.Open.pRank r ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
      c.S.M.subtype) = 0 → False

private theorem isLieFam811_psp6 {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .PSp 3 r f) : IsLieFam811 X .psp6 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, hr3, h⟩

private theorem isLieFam811_omega7 {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .POmegaOdd 3 r f) : IsLieFam811 X .omega7 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1,
    (CFSG.Blueprint.LieModel.admissible h).2.2.2, hr3, h⟩

private theorem isLieFam811_pomega8m {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .POmegaMinus 4 r f) : IsLieFam811 X .pomega8m r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, hr3, h⟩

private theorem isLieFam811_l4_psl {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 1)
    (h : LieModel X .PSL 4 r f) : IsLieFam811 X .l4 r f := by
  refine ⟨(CFSG.Blueprint.LieModel.admissible h).1, ?_, Or.inl ⟨hmod, h⟩⟩
  rintro h2
  rw [h2] at hmod
  norm_num at hmod

private theorem isLieFam811_l4_psu {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 2)
    (hne2 : r ^ f ≠ 2) (h : LieModel X .PSU 4 r f) : IsLieFam811 X .l4 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, hne2, Or.inr ⟨hmod, h⟩⟩

private theorem isLieFam811_l6_psl {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 2)
    (h : LieModel X .PSL 6 r f) : IsLieFam811 X .l6 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, Or.inl ⟨hmod, h⟩⟩

private theorem isLieFam811_l6_psu {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 1)
    (h : LieModel X .PSU 6 r f) : IsLieFam811 X .l6 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, Or.inr ⟨hmod, h⟩⟩

private theorem isLieFam811_l7_psl {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 2)
    (h : LieModel X .PSL 7 r f) : IsLieFam811 X .l7 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, Or.inl ⟨hmod, h⟩⟩

private theorem isLieFam811_l7_psu {X : Type} [Group X] {r f : ℕ} (hmod : r ^ f % 3 = 1)
    (h : LieModel X .PSU 7 r f) : IsLieFam811 X .l7 r f :=
  ⟨(CFSG.Blueprint.LieModel.admissible h).1, Or.inr ⟨hmod, h⟩⟩

private theorem false_of_lie_case (c : Counterexample4 G)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L)
    (hK : KInputs811)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (h8 : Section8L4Residual c)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar))
    (hON : ¬ ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (h227 : ¬ LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    {fam : LieFam811} {r f : ℕ} (hlie : IsLie811 c.Lbar fam r f)
    {p : ℕ} (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p) : False := by
  have hPL : ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P c.S.M → P ≤ c.L :=
    fun P hP => c.le_L_of_K2 h811 hK.k2 hZ hON h227 hP
  obtain ⟨h⟩ := Counterexample4.exists_case811Sylow_of_K6 c hK.k6a hK.k6b hlie hPL
  by_cases hpr : p = r
  · subst r
    by_cases hl4 : fam = .l4 ∧ f = 1
    · obtain ⟨rfl, rfl⟩ := hl4
      by_cases hC : 1 ≤ CFSG.Open.pRank p
          ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
            c.S.M.subtype)
      · exact h.false_of_l4_of_one_le_pRank_ker hK.k6c hK.k6L4 hlie hp h76
          (hK.k6Z c.Lbar p hlie (c.five_le_of_mem_sigma hp)) hC
      · have hC0 : CFSG.Open.pRank p
            ((CFSG.GroupTheory.conjModPCore 2 c.L c.S.M c.le_normalizer_L).ker.map
              c.S.M.subtype) = 0 := by omega
        refine h8 h p hlie ?_ hp h76 hC0
        intro q hq
        by_contra hqp
        exact h.false_of_ne_char hK.k6c hK.k7 hlie hq
          (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.conclusion76 c hq hSE) hqp
    · exact h.false_of_eq_char hK.k6c hK.k6r hlie hp h76 hl4
  · exact h.false_of_ne_char hK.k6c hK.k7 hlie hp h76 hpr

theorem Counterexample4.false_of_quasisimpleModOTwo (c : Counterexample4 G)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK : KInputs811)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (h8 : Section8L4Residual c) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hK5 : K5 :=
    ⟨k5A9_holds, k5A10_holds, k5A11_holds, hK.k5J3, hK.k5ONan, hK.k5U42, hK.k5L227⟩
  obtain ⟨p, hp⟩ := c.sigma_nonempty
  have h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.conclusion76 c hp hSE
  have hqs : CFSG.Open.IsQuasisimple c.Lbar := c.isQuasisimple_lbar h811
  have hqsC : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff c.Lbar).2.2.1.mpr hqs
  have hcat : CFSG.Open.IsCatalogGroup (c.Lbar ⧸ Subgroup.center c.Lbar) :=
    c.isCatalogGroup_lbar h811
  have hodd : Odd (Nat.card (Subgroup.center c.Lbar)) := c.odd_card_center_lbar
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup c.Lbar) = 3 := c.pRank_three_lbar
  by_cases hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar
  ·
    exact c.false_of_threeCover_ONan hK.k3 hK5 (hK.k3Out c.Lbar hON) hON hp h76
  · rcases hK.k1 c.Lbar hqs hcat hodd hrank with hON' | ⟨hZ, hrest⟩
    · exact absurd hON' hON
    · by_cases h227 : LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3
      ·
        exact c.false_of_L227 h811 hK.k4a hK.k4b h227 hZ hp h76
      · rcases hrest with hsmall | hthree | hfour | hj3
        ·
          rcases hsmall with h9 | h10 | h11
          · exact c.false_of_small h811 hK.k2 hK5 hZ hON h227 hp h76 (Or.inl h9)
          · exact c.false_of_small h811 hK.k2 hK5 hZ hON h227 hp h76
              (Or.inr (Or.inl h10))
          · exact c.false_of_small h811 hK.k2 hK5 hZ hON h227 hp h76
              (Or.inr (Or.inr (Or.inl h11)))
        ·
          rcases hthree with h227' | hpsp
          · exact absurd h227' h227
          · exact c.false_of_small h811 hK.k2 hK5 hZ hON h227 hp h76
              (Or.inr (Or.inr (Or.inr (Or.inr hpsp))))
        ·
          rcases hfour with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8' | h9
          · obtain ⟨r, f, hr3, hm⟩ := h1
            exact false_of_lie_case c h811 hK hSE h8 hZ hON h227
              ⟨hqsC, hodd, isLieFam811_psp6 hr3 hm⟩ hp h76
          · obtain ⟨r, f, hr3, hm⟩ := h2
            exact false_of_lie_case c h811 hK hSE h8 hZ hON h227
              ⟨hqsC, hodd, isLieFam811_pomega8m hr3 hm⟩ hp h76
          · obtain ⟨r, f, hmod, hm⟩ := h3
            exact false_of_lie_case c h811 hK hSE h8 hZ hON h227
              ⟨hqsC, hodd, isLieFam811_l4_psl hmod hm⟩ hp h76
          · obtain ⟨r, f, hmod, hne2, hm⟩ := h4
            exact false_of_lie_case c h811 hK hSE h8 hZ hON h227
              ⟨hqsC, hodd, isLieFam811_l4_psu hmod hne2 hm⟩ hp h76
          · obtain ⟨r, f, hmod, hm⟩ := h5
            exact false_of_lie_case c h811 hK hSE h8 hZ hON h227
              ⟨hqsC, hodd, isLieFam811_l6_psl hmod hm⟩ hp h76
          · obtain ⟨r, f, hmod, hm⟩ := h6
            exact false_of_lie_case c h811 hK hSE h8 hZ hON h227
              ⟨hqsC, hodd, isLieFam811_l6_psu hmod hm⟩ hp h76
          · obtain ⟨r, f, hmod, hm⟩ := h7
            exact false_of_lie_case c h811 hK hSE h8 hZ hON h227
              ⟨hqsC, hodd, isLieFam811_l7_psl hmod hm⟩ hp h76
          · obtain ⟨r, f, hmod, hm⟩ := h8'
            exact false_of_lie_case c h811 hK hSE h8 hZ hON h227
              ⟨hqsC, hodd, isLieFam811_l7_psu hmod hm⟩ hp h76
          · obtain ⟨r, f, hr3, hm⟩ := h9
            exact false_of_lie_case c h811 hK hSE h8 hZ hON h227
              ⟨hqsC, hodd, isLieFam811_omega7 hr3 hm⟩ hp h76
        ·
          exact c.false_of_small h811 hK.k2 hK5 hZ hON h227 hp h76
            (Or.inr (Or.inr (Or.inr (Or.inl hj3))))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
