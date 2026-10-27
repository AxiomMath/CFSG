module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamE9
import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowRuJ4

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint

namespace Hering129C

theorem census_false_of_automizer {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q}
    {I X : Subgroup Q} {f : ↥I →* Lb} (hD : Census129 c a I X f)
    (hA : Nonempty (Asc83Table.Automizer (Subgroup.zpowers a ⊔ Subgroup.zpowers c) ≃*
      Asc83Table.GL23)) : False := by
  obtain ⟨n, hn, hns⟩ := Sec4.Ronan148S.exists_move_of_automizer (census_abar_isElemAbelian hD)
    (census_card_abar hD) hA (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)) (c_ne_one hD)
  exact hns (hD.gamma hn)

theorem kFCensus46Five_RuJ4 :
    KFCensusOn (fun Q _ => Nonempty (Q ≃* NativeSporadic.Carrier .Ru) ∨
      Nonempty (Q ≃* NativeSporadic.Carrier .J4)) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  have hE := Sec4.Ronan148S.isElementaryAbelian_of_isElemAbelian (census_abar_isElemAbelian hD)
  rcases hQ with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact census_false_of_automizer hD
      (Sec4.Ronan148S.ru_automizer_all ⟨e⟩ _ hE (census_card_abar hD))
  · exact census_false_of_automizer hD
      (Sec4.Ronan148S.j4_automizer_all ⟨e⟩ _ hE (census_card_abar hD))

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
