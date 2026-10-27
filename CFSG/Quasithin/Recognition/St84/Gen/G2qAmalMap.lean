module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalDefs

import CFSG.Quasithin.Recognition.St84.Gen.CenterPCoreMap
import CFSG.Quasithin.Recognition.St84.Gen.NatSecMap
import CFSG.Quasithin.Recognition.F112RShapes
import CFSG.Quasithin.Recognition.GoldschmidtF112RTransport
import CFSG.Quasithin.Background.SpecialPGroupMulEquiv

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin

theorem G2qLocalData.of_mulEquiv {G G' : Type*} [Group G] [Group G'] {L1 L2 S : Subgroup G}
    {L1' L2' S' : Subgroup G'} {f : ℕ} (e1 : ↥L1 ≃* ↥L1') (e2 : ↥L2 ≃* ↥L2')
    (hS : Nat.card S = Nat.card S')
    (hinf : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) =
      Nat.card ↥(pCoreOf 2 L1' ⊓ pCoreOf 2 L2'))
    (h : G2qLocalData L1' L2' S' f) : G2qLocalData L1 L2 S f := by
  refine
    { card_S := hS.trans h.card_S
      special_left := CFSG.Quasithin.IsSpecialPow.of_mulEquiv (pCoreOfMulEquiv e1.symm 2)
        h.special_left
      center_left := centerOf_pCoreOf_eq_of_mulEquiv e1 h.center_left
      special_right := CFSG.Quasithin.IsSpecialPGroup.of_mulEquiv (pCoreOfMulEquiv e2.symm 2)
        h.special_right
      card_right := (card_pCoreOf_of_mulEquiv e2 2).trans h.card_right
      nat_right := ?_
      card_inf := hinf.trans h.card_inf }
  obtain ⟨F, hFld, hFintype, hcardF, α, hαsurj, hαker, hnatZ, W', hZ'W', hW'Q', hW'card,
    hcommW', hnatQ'⟩ := h.nat_right
  have hα := isNatSecOf_centerOf_of_mulEquiv e2 hαsurj hαker hnatZ
  obtain ⟨W, hZW, hWQ, hWcard, hcommW, hWmem⟩ := exists_sub_of_mulEquiv e2 hZ'W' hW'Q' hcommW'
  refine ⟨F, hFld, hFintype, hcardF, α.comp e2.toMonoidHom, hα.1, hα.2.1, hα.2.2, W, hZW, hWQ,
    hWcard.trans hW'card, hcommW, ?_⟩
  simpa using IsNatSecOf.of_mulEquiv (e := e2.symm) (α := α)
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L2') (CFSG.LieType.BorelTits.pCoreOf_le 2 L2)
    (mem_pCoreOf_iff_of_mulEquiv e2.symm 2) (fun x => by simpa using (hWmem (e2.symm x)).symm)
    hnatQ'

end CFSG.Quasithin.F112R.St84

end
