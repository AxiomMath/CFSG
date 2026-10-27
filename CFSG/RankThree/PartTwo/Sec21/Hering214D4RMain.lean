module

public import CFSG.RankThree.PartTwo.Sec21.Hering214D4RC0
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.Assembly (IsElemAbelian)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartTwo.Sec19

section Main


theorem item214BarLie3D4'_holds : Item214BarLie3D4' := by
  intro X _ _ ⟨n, hn0, hev, hX⟩ Ē hE3 hE9 hR
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    exists_mulEquiv_graphFixedRootGroup_card .D4 Nat.prime_two hn0 hX.2
  have P : D4Par n K σ := ⟨hn0, hK, hσ⟩
  have hn2 : 2 ≤ n := by
    obtain ⟨m, hm⟩ := hev
    omega
  refine EInvFour.of_map_mulEquiv e ?_
  exact eInvFour_C0_of_reflectsE P hn2 hev (CFSG.Open.IsElemAbelian.map hE3 _)
    (by rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hE9])
    (hR.map_mulEquiv e)

end Main

end CFSG.RankThree.PartTwo.Sec21.Hering214
