module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SENeDRed
import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

@[expose] def Step138ENeDSevenT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (x y t : G),
    Ronan138S.Frame138Base A L E F c x y t → Subgroup.zpowers ⁅x, y⁆ ∈ omegaA E →
    ∀ K : Subgroup G, K ∈ lA E ⁅x, y⁆ → ⁅x, y⁆ ∈ K → HypT E →
      (Sec4.IsSLThreePiTwo (lBarA ⁅x, y⁆ K E) ∨
        (Sec4.IsHeisCentral (lBarA ⁅x, y⁆ K E) (K ⧸ aschbacherSolvableCore 3 K) ∧
          Subgroup.normalizer (E : Set G) ≤
            Subgroup.normalizer (Subgroup.zpowers ⁅x, y⁆ : Set G))) → False

@[expose] def Step138ENeDHeisT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (x y t : G),
    Ronan138S.Frame138Base A L E F c x y t → Subgroup.zpowers ⁅x, y⁆ ∈ omegaA E →
    ∀ K : Subgroup G, K ∈ lA E ⁅x, y⁆ → ⁅x, y⁆ ∈ K → HypT E →
      Sec4.IsHeisCentral (lBarA ⁅x, y⁆ K E) (K ⧸ aschbacherSolvableCore 3 K) →
      Subgroup.normalizer (E : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers ⁅x, y⁆ : Set G) → False

end CFSG.RankThree.PartTwo.Sec13

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem step138ENeDSeven_of (hT : Step138ENeDSevenT) : Step138ENeDSeven := by
  intro G _ _ A c L E F x y t hfr hΩ K hK hdK h7
  rcases hfr.hH.2.2.2.2.2.2.2.1 with hS | hT'
  · exact hS.2.2 _ hΩ K hK hdK
  · exact hT G A c L E F x y t hfr hΩ K hK hdK hT' h7

theorem step138ENeDSevenT_of (h131 : Item131) (hspor : SporadicModels131)
    (hHeis : Step138ENeDHeisT) : Step138ENeDSevenT := by
  intro G _ _ A c L E F x y t hfr hΩ K hK hdK hT h7
  rcases h7 with hSL | ⟨hH, hN⟩
  · have h := hfr.hH.1
    have hXF := mem_partTwoF_of_hyp138 hfr.hH
    have hD : Sec13Data G E ⁅x, y⁆ K :=
      { h.toPartTwoStanding with
        partTwoS_eq := h.partTwoS_eq
        mem_partTwoF := hXF.1
        not_mem_partTwoT := hXF.2
        zpowers_mem_omegaA := hΩ
        mem_lA := hK }
    exact notSLTwoOfHypT_of h131 hspor G E ⁅x, y⁆ K hD hT hSL
  · exact hHeis G A c L E F x y t hfr hΩ K hK hdK hT hH hN

end CFSG.RankThree.PartTwo.Sec13.Ronan138S
