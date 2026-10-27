module

public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalDefs

import CFSG.Quasithin.Recognition.F112RShapes
import CFSG.Quasithin.Recognition.GoldschmidtF112RTransport
import CFSG.Quasithin.Recognition.St84.Gen.CenterPCoreMap

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin

theorem D4qLocalData.of_mulEquiv {G G' : Type*} [Group G] [Group G'] {L1 L2 S : Subgroup G}
    {L1' L2' S' : Subgroup G'} {f : ℕ} (e1 : ↥L1 ≃* ↥L1') (e2 : ↥L2 ≃* ↥L2')
    (hS : Nat.card S = Nat.card S') (h : D4qLocalData L1' L2' S' f) :
    D4qLocalData L1 L2 S f := by
  refine
    { card_S := hS.trans h.card_S
      special_left := CFSG.Quasithin.IsSpecialPow.of_mulEquiv (pCoreOfMulEquiv e1.symm 2)
        h.special_left
      center_left := centerOf_pCoreOf_eq_of_mulEquiv e1 h.center_left
      irred_left := ?_
      card_right := (card_pCoreOf_of_mulEquiv e2 2).trans h.card_right
      nat_right := ?_
      mid_right := ?_ }
  · intro W hZW hWQ hWnorm
    exact eq_centerOf_or_eq_pCoreOf_of_mulEquiv e1 h.irred_left hZW hWQ hWnorm
  · obtain ⟨F, hFld, hFintype, hcardF, α, hαsurj, hαker, hnat⟩ := h.nat_right
    exact ⟨F, hFld, hFintype, hcardF, α.comp e2.toMonoidHom,
      isNatSecOf_centerOf_of_mulEquiv e2 hαsurj hαker hnat⟩
  · obtain ⟨W', hZW', hW'Q, hW'card, hcomm⟩ := h.mid_right
    obtain ⟨W, hZW, hWQ, hWcard, hcommW, -⟩ := exists_sub_of_mulEquiv e2 hZW' hW'Q hcomm
    exact ⟨W, hZW, hWQ, hWcard.trans hW'card, hcommW⟩

end CFSG.Quasithin.F112R.St84

end
