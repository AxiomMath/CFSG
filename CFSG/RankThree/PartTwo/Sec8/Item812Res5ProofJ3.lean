module

public import CFSG.RankThree.PartTwo.Sec8.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

namespace Item812Res5

theorem nonempty_center_quot_of_mulEquiv {L' M J : Type*} [Group L'] [Group M] [Mul J]
    (e : L' ≃* M) (h : Nonempty (L' ⧸ Subgroup.center L' ≃* J)) :
    Nonempty (M ⧸ Subgroup.center M ≃* J) := by
  obtain ⟨f⟩ := h
  exact ⟨(QuotientGroup.congr (Subgroup.center L') (Subgroup.center M) e
    (Subgroup.map_center_eq e)).symm.trans f⟩

end Item812Res5

open Item812Res5

@[expose] def KF89NotJ3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y →
      ¬ (KFacts.InducesStdKind Y c .field ∨ KFacts.InducesStdKind Y c .graphField) ∧
        ¬ (KFacts.InducesStdKind Y b .field ∨ KFacts.InducesStdKind Y b .graphField) →
      Nonempty (perfectResidual (barCentralizer (Subgroup.zpowers a) X) ≃*
        alternatingGroup (Fin 6)) →
      ¬ Nonempty ((Y ⧸ aschbacherSolvableCore 3 Y) ⧸
        Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) ≃* NativeSporadic.J3)

end CFSG.RankThree.PartTwo.Sec8
