module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Blueprint

@[expose] def Item4_30 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → partTwoE G = partTwoF G →
    aschbacherSolvableCore 3 G = ⊥ → ∀ A : Subgroup G, Late.IsE27 A →
    ∀ L : Subgroup G, IsComponent L → ∀ a : G,
      A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers a → orderOf a = 3 →
    ∀ c ∈ A, c ∉ Subgroup.zpowers a → ∀ B : Subgroup G,
      Subgroup.zpowers c ⊔ B = A → Subgroup.zpowers c ⊓ B = ⊥ →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (B : Set G) →
    ∀ R ∈ invariantPiSubgroups L A (piOf 2), R ≠ ⊥ → ⁅R, Subgroup.zpowers c⁆ = R →
      (∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField) ∨
        Nonempty (L ≃* NativeSporadic.M12) ∨ Nonempty (L ≃* NativeSporadic.J2)

end CFSG.RankThree.PartTwo.Sec4
