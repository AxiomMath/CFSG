module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Sec717CRSylowStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    (∃ h ∈ H0 M Z, conjSubgroup h Z0 ≤ NormH0 M Z Z0 ∧ ¬ conjSubgroup h Z0 ≤ hc.CN t) →
    ¬ NormH0L M Z L ≤ NormH0 M Z Z0 →
    ∀ z ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), z ≠ 1 →
      ∀ h : ↥(bar M Q (H0 M Z)),
        h * z * h⁻¹ ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)) →
        h * z * h⁻¹ ∉ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) →
          ∃ T : Sylow 2 ↥(conjSubgroup h
              ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))),
            Subgroup.map (conjSubgroup h
                ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)))).subtype T ≤
              Subgroup.normalizer
                ((bar M Q L).subgroupOf (bar M Q (H0 M Z)) : Set ↥(bar M Q (H0 M Z)))

end CFSG.RankThree.GF2n.Stroth80
