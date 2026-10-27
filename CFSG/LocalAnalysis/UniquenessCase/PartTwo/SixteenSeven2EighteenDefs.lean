module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Insp18 (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) (L : Subgroup G)
    (g : G) (Δ : Set (Subgroup G)) : Prop where
  ge : D.k + 1 ≤ mBar D.M V₀ V hV
  big : ∀ J ∈ deltaConj Δ g, D.k + 1 < rk ↥J
  disj : ∀ u ∈ V ⊓ conjSubgroup D.M g,
    E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({u} : Set G)) ≤ D.k + 1 →
      ∀ J ∈ deltaConj Δ g, conjSubgroup J u = J ∨ J ⊓ conjSubgroup J u = ⊥
  k_eq_one : Case168_2 D V₀ V hV L → D.k = 1
  dist₂ : Case168_2 D V₀ V hV L → ∀ u ∈ V ⊓ conjSubgroup D.M g,
    (∀ J ∈ deltaConj Δ g, conjSubgroup J u = J) →
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({u} : Set G)) = D.k + 1 →
        ∀ J ∈ deltaConj Δ g, ¬ J ≤ centralizer ({u} : Set G)
  dist : ¬ Case168_2 D V₀ V hV L → ∀ u ∈ V ⊓ conjSubgroup D.M g,
    (∀ J ∈ deltaConj Δ g, conjSubgroup J u = J) →
      E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ centralizer ({u} : Set G)) = D.k + 1 →
        ∀ J ∈ deltaConj Δ g, J ≤ centralizer ({u} : Set G) ∨
          D.k + 1 ≤ E3.mQuot J (J ⊓ centralizer ({u} : Set G))

theorem s16c167_k_le_two (D : Data G) : D.k ≤ 2 := by
  unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
  split_ifs <;> omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
