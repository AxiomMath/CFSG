module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item4_26Theta : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ L ∈ thetaComponents 3 G,
    ∀ c : G, orderOf c = 3 → ∀ K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {c}),
      (IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)) ∨
        IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 7)) ∨
        IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) Blueprint.NativeSporadic.M22 ∨
        IsSLThreePi (K ⧸ aschbacherSolvableCore 3 K)) →
      inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≠ ⊥ →
      inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≤ Subgroup.center G →
      L = K ⊔ inSubgroup (aschbacherSolvableCore 3) L ∨
      (∃ n : ℕ, 1 ≤ n ∧ IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) ∧
        IsSLThreePiAt (K ⧸ aschbacherSolvableCore 3 K) (2 ^ n)) ∨
      (IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) Blueprint.NativeSporadic.ON ∧
        IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))

end CFSG.RankThree.PartTwo.Sec4
