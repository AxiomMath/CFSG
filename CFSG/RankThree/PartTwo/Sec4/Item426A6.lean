module

public import CFSG.RankThree.PartTwo.Sec4.Statements426

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item4_26ThetaA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → ∀ L ∈ thetaComponents 3 G,
    ∀ c : G, orderOf c = 3 → ∀ K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {c}),
      IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)) →
      inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≠ ⊥ →
      inSubgroup (CFSG.pCore 3) (K ⊓ Subgroup.centralizer (K : Set G)) ≤ Subgroup.center G →
      L = K ⊔ inSubgroup (aschbacherSolvableCore 3) L ∨
      (∃ n : ℕ, 1 ≤ n ∧ IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) ∧
        IsSLThreePiAt (K ⧸ aschbacherSolvableCore 3 K) (2 ^ n)) ∨
      (IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) Blueprint.NativeSporadic.ON ∧
        IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6)))

theorem item4_26ThetaA6_of_item4_26Theta (h : Item4_26Theta) : Item4_26ThetaA6 :=
  fun G _ _ hG L hL c hc K hK hA6 hne hle => h G hG L hL c hc K hK (Or.inl hA6) hne hle

end CFSG.RankThree.PartTwo.Sec4
