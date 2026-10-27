module

public import CFSG.Blueprint.Catalog

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

@[expose] def untwistedTag : StatedLieTag → Option Tag
  | .G2 => some .G2
  | .F4 => some .F4
  | .E6 => some .E6
  | .E7 => some .E7
  | .E8 => some .E8
  | _ => none

theorem lieModel_untwisted_iff {G : Type} [Group G] {t : StatedLieTag} {τ : Tag}
    (ht : untwistedTag t = some τ) {n f : ℕ} :
    LieModel G t n 2 f ↔ n = 0 ∧ StatedLieAdmissible t 0 2 f ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
        Nonempty (G ≃* AdjointQuotient τ K) := by
  cases t <;> simp only [untwistedTag, reduceCtorEq, Option.some.injEq] at ht
  all_goals subst ht
  all_goals
    simp only [LieModel, ChevalleyExceptionalModel, UntwistedChevalleyModel, classicalTags,
      chevalleyExceptionalTags, reeTitsTags, Finset.mem_insert, Finset.mem_singleton,
      reduceCtorEq, false_and, false_or, or_false, and_false, true_and, or_true]

end CFSG.RankThree.PartOne.Sec66T
