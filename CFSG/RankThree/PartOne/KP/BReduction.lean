module

public import CFSG.RankThree.PartOne.KP.BLevi
public import CFSG.RankThree.PartOne.KP.SectionCover

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.LowTwoRank

theorem sectionsForceEvenRankFour_of_unitary_levi_component {X Sg : Type} [Group X] [Group Sg]
    [Finite Sg] (ι : X ≃* Sg) {s : Sg}
    {K : Subgroup (Subgroup.centralizer ({s} : Set Sg))} (hK : IsQuasisimple K)
    (hZ : Nat.card (Subgroup.center K) = 2) {C : Type} [Group C]
    (eQ : K ⧸ Subgroup.center K ≃* C) (L : Subgroup C)
    (e : L ≃* StatedProj (StatedSU 6 (2 ^ 1) CFSG.Fischer.F4))
    (U9 : Subgroup (StatedProj (StatedSU 6 (2 ^ 1) CFSG.Fischer.F4)))
    (hU9 : IsElementaryAbelian 2 U9) (hc9 : Nat.card U9 = 2 ^ 9) :
    SectionsForceEvenRankFour X := by
  obtain ⟨U, hU, hUc⟩ := elementary_two_five_of_levi L e U9 hU9 hc9
  have hS := sectionsForceEvenRankFour_of_centralizer_component hK (by rw [hZ]; exact even_two) eQ
    U hU hUc (fun Y _ _ f hf hk => central_cover_of_levi L e Y f hf hk)
  intro G _ _ H K' _ ⟨φ⟩
  exact hS G H K' ⟨φ.trans ι⟩

end CFSG.RankThree.PartOne
