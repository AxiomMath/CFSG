module

public import CFSG.RankThree.PartTwo.Sec12.Hering129CFamE9
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRankTwo
import CFSG.RankThree.PartTwo.Sec4.Ronan148HRow425F4
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129C

section Gen

variable {Q Lb : Type} [Group Q] [Finite Q] [Group Lb] {c a : Q} {I X : Subgroup Q}
  {f : ↥I →* Lb} {H : Type} [Group H]

theorem census_false_of_e9Move (hD : Census129 c a I X f) (e : Q ≃* H)
    (h : Sec4.Ronan148S.E9Move H) : False := by
  obtain ⟨n, hn, hns⟩ := h ((Subgroup.zpowers a ⊔ Subgroup.zpowers c).map e.toMonoidHom)
    (CFSG.Open.IsElemAbelian.map (census_abar_isElemAbelian hD) _)
    (by rw [Subgroup.card_map_of_injective e.injective, census_card_abar hD]) (e c)
    ⟨c, Subgroup.mem_sup_right (Subgroup.mem_zpowers c), rfl⟩
    (fun h1 => c_ne_one hD (e.injective (h1.trans (map_one e).symm)))
  exact hns (census_gamma_map hD e hn)

end Gen

section Twisted


theorem kFCensus46SixF4_twisted :
    KFCensusOn (fun Q _ => ∃ f : ℕ, Blueprint.ReeTitsModel Q .twistedF4 2 f) := by
  intro Q Lb _ _ _ c a I X f hQ hD
  exfalso
  obtain ⟨f', hf'⟩ := hQ
  obtain ⟨-, a', -, -, K, _, _, _, hK, ⟨e⟩⟩ := Sec4.exists_mulEquiv_reeGamma hf'
  exact census_false_of_e9Move hD e (Sec4.Ronan148H.e9Move_reeGamma a' K hK)

end Twisted

end Hering129C

end CFSG.RankThree.PartTwo.Sec12
