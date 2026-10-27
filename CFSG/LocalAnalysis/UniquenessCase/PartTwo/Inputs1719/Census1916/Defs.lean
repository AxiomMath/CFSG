module

public import CFSG.Foundations.Basic
public import CFSG.GroupTheory.PCore.Construction
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916

open CFSG CFSG.Open

structure RankHyp1916 (Y : Type) [Group Y] [Finite Y] : Prop where
  quasisimple : CFSG.IsQuasisimple Y
  pCore_two : CFSG.pCore 2 Y = ⊥
  pRank_odd : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup Y) ≤ 3

theorem RankHyp1916.false_of_injective {Y G : Type} [Group Y] [Finite Y] [Group G] [Finite G]
    (h : RankHyp1916 Y) (φ : G →* Y) (hφ : Function.Injective φ) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (h4 : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup G)) : False := by
  have := h.pRank_odd r hr hr2
  have := h4.trans (CFSG.SectionRank.pRank_top_le_of_injective hr.one_lt φ hφ)
  omega

theorem RankHyp1916.false_of_mulEquiv {Y G : Type} [Group Y] [Finite Y] [Group G] [Finite G]
    (h : RankHyp1916 Y) (e : G ≃* Y) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h4 : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup G)) : False :=
  h.false_of_injective e.toMonoidHom e.injective hr hr2 h4

@[expose] def Census1916SurvPSL : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), RankHyp1916 Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL n 2 f → 5 ≤ n → f = 1 ∧ n ≤ 7

@[expose] def Census1916SurvPSU : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), RankHyp1916 Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU n 2 f → 5 ≤ n → n = 5 ∧ f = 2

@[expose] def Census1916SurvPSp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), RankHyp1916 Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSp n 2 f → 4 ≤ n → False

@[expose] def Census1916SurvPOmegaPlus : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), RankHyp1916 Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaPlus n 2 f → False

@[expose] def Census1916SurvPOmegaMinus : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ), RankHyp1916 Y →
    StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaMinus n 2 f → 5 ≤ n → False

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916
