module

public import CFSG.RankThree.PartTwo.Sec3.Item321

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Item321Count : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X L T : Subgroup G) (n : ℕ),
    CFSG.generalizedFitting X = CFSG.pCore 2 X → L ∈ oTwoComponentsIn X →
    X ≤ Subgroup.normalizer (L : Set G) →
    CFSG.ABGLocalTools.IsSylowOf 2 T X → L ⊔ T = X → Odd n →
    Nonempty (L ⧸ CFSG.pCore 2 L ≃* projSL 3 (GaloisField 2 n)) →
      (X ≤ Subgroup.normalizer (thompsonOf T : Set G) ∨
          ⁅omegaZOf (CFSG.Open.pCoreOf 2 X), L⁆ = ⊥) ∨
        (L ⊔ CFSG.Open.pCoreOf 2 X = X ∧
          ∀ (r : ℕ) (Vs : Fin (r + 1) → Subgroup G),
            IsChiefSeriesUnder L (omegaZOf (CFSG.Open.pCoreOf 2 X)) r Vs →
              ∀ i j k : Fin r, i < j → j < k → ¬ ⁅Vs i.succ, L⁆ ≤ Vs i.castSucc →
                ¬ ⁅Vs j.succ, L⁆ ≤ Vs j.castSucc → ¬ ⁅Vs k.succ, L⁆ ≤ Vs k.castSucc → False)

end CFSG.RankThree.PartTwo.Sec3.Sims321
