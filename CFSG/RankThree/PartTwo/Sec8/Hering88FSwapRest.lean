module

public import CFSG.RankThree.PartTwo.Sec8.Hering88FCovered

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def KF88Case1ClassBSwapRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    ∀ Y ∈ thetaComponentsAt 3 a, sec8I L a ⊔ sec8J X a ≤ Y → ∀ x : G, x = b → x ≠ c →
      (KFacts.InducesStdKind Y x .field ∨ KFacts.InducesStdKind Y x .graphField) →
      ∀ (A₀ : Subgroup G) (d' : G) (m : ℕ), Odd m → Case83One Y x A₀ d' m →
      ¬ ClassBCovered b c x L Y n m →
      ∀ d ∈ Subgroup.closure ({c, b} : Set G), d ∉ Subgroup.zpowers x → d ∈ A → d ^ 3 = 1 →
        ∀ hdN : d ∈ Subgroup.normalizer (Y : Set G),
          KFacts.IsInnerAut (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) →
          Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩) ≠ 1 →
          (∃ E : Subgroup G, E ≤ A ∧ d ∈ E ∧ InvTwoBarNontrivial E Y) →
          Nonempty (imageModTheta Y
            (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) ≃*
              projSL 2 (GaloisField 2 (3 * m)))

end CFSG.RankThree.PartTwo.Sec8
