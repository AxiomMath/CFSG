module

public import CFSG.RankThree.GF2n.Tim79aSec23Degenerate
public import CFSG.RankThree.GF2n.Tim79aWCQ
public import CFSG.RankThree.GF2n.Tim79aSec23NoSqE1

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

@[expose] def Tim79aCase1Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), MinCexWCQ M V Q P H →
    Nat.card (barOf V H V) = 2 → barOf V H (xOf V H) = oddCoreX V H ⊔ barOf V H V → False

@[expose] def Tim79aSquareStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), MinCexWCQ M V Q P H →
    Sec23Data V H → (∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4) →
    (∃ u ∈ Dtilde V H, ∃ v ∈ Dtilde V H, u ≠ v ∧ Commute u v ∧ u * v ∈ Dtilde V H) → False

@[expose] def Tim79aTransvectionStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M V Q P H : Subgroup G), MinCexWCQ M V Q P H →
    Sec23Data V H → (∀ d ∈ Dy V H, ∀ e ∈ Dy V H, orderOf (d * e) ≠ 4) →
    (¬ ∃ u ∈ Dtilde V H, ∃ v ∈ Dtilde V H, u ≠ v ∧ Commute u v ∧ u * v ∈ Dtilde V H) →
    CFSG.Timmesfeld.Transvection.TransvectionHyp (Xbar V H ⧸ Subgroup.center (Xbar V H))
      {A | ∃ d ∈ Dy V H,
        A = Subgroup.zpowers (QuotientGroup.mk' (Subgroup.center (Xbar V H)) d)} → False

section Certified


theorem tim79aStatementWCQ_of_inputs (h1 : Tim75aTINotWCRoot) (h2 : OddTranspNoSqE1Dich)
    (hC1 : Tim79aCase1Statement) (hSq : Tim79aSquareStatement)
    (hTr : Tim79aTransvectionStatement) : Tim79aStatementWCQ := by
  apply tim79aStatementWCQ_of_not_minCexWCQ
  intro G _ _ M V Q P H hc
  rcases hc.toMinCex.sec23_dichotomy with ⟨h21, h22⟩ | hd
  · exact hC1 G M V Q P H hc h21 h22
  · have hdeg := hc.toMinCex.degenerate_of_inputs h1 hd
    by_cases hsq : ∃ u ∈ Dtilde V H, ∃ v ∈ Dtilde V H, u ≠ v ∧ Commute u v ∧ u * v ∈ Dtilde V H
    · exact hSq G M V Q P H hc hd hdeg hsq
    · exact hTr G M V Q P H hc hd hdeg hsq
        (hc.toMinCex.transvectionHyp_of_noSquare' h2 hd hdeg hsq)

end Certified

end CFSG.RankThree.GF2n.Tim79a
