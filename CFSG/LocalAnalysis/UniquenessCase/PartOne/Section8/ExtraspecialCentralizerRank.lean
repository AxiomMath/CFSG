module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRankTits

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped commutatorElement

theorem two_le_pRank_three_centralizer_of_extraspecial
    {G : Type} [Group G] [Finite G] {Q X : Subgroup G} {x y : G}
    (hxQ : x ∈ Q) (hyQ : y ∈ Q)
    (hQX : Q ≤ Subgroup.centralizer (X : Set G))
    (hx3 : x ^ 3 = 1) (hz : ⁅x, y⁆ ≠ 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) :
    2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G)) := by
  let H : Subgroup G := Subgroup.centralizer (X : Set G)
  let xH : H := ⟨x, hQX hxQ⟩
  let yH : H := ⟨y, hQX hyQ⟩
  have hxH3 : xH ^ 3 = 1 := Subtype.ext (by simpa [xH] using hx3)
  have hzH : ⁅xH, yH⁆ ≠ 1 := by
    intro h
    apply hz
    have hv : H.subtype ⁅xH, yH⁆ = (1 : G) := by rw [h]; rfl
    rw [map_commutatorElement] at hv
    simpa [xH, yH] using hv
  have hzxH : Commute ⁅xH, yH⁆ xH := by
    refine Commute.of_map (f := H.subtype) H.subtype_injective ?_
    rw [map_commutatorElement]
    simpa [xH, yH] using hzx
  have hzyH : Commute ⁅xH, yH⁆ yH := by
    refine Commute.of_map (f := H.subtype) H.subtype_injective ?_
    rw [map_commutatorElement]
    simpa [xH, yH] using hzy
  have h :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeRank.two_le_pRank_three_of_extraspecial
      (G := H) hxH3 hzH hzxH hzyH
  rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H] at h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
