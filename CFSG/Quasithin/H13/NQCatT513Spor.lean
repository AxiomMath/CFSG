module

public import CFSG.Quasithin.H13.NQCatT513Lat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Model
public import CFSG.Sporadic.J2
import all CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu

public section

namespace CFSG.Quasithin.H13.NQCat.T513P

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Sporadic.SmallF2 CFSG.QuasithinUnique.Ch1.SporLat.HS CFSG.QuasithinUnique.Ch1.SporLat.Ru
open CFSG.Sporadic.HS.Native (hsData)
open CFSG.Sporadic.Ru.Native (ruData)

theorem cycOddPerm_j2Grp :
    CycOddPerm ↥CFSG.Sporadic.J2.J fun _ => False := by
  have hS : Nat.card ↥A312J2.j2CtxA.S = 2 ^ 7 :=
    card_of_isSylowTwoOf_top A312J2.j2A_sylow (m := 4725)
      (by rw [CFSG.Sporadic.J2.card_J]; norm_num) (by decide)
  exact cycOddPerm_of_list A312J2.j2A_sylow (E2P.SporB.lat_all _ A312J2.j2A_hL)
    (fun j hj => by rw [hS]; exact A312J2.j2A_card hj) (by decide) (N := 4725)
    (by rw [CFSG.Sporadic.J2.card_J, hS]; norm_num) (by norm_num)

theorem cycOddPerm_j2 :
    CycOddPerm (CFSG.Blueprint.NativeSporadic.Carrier .J2) fun _ => False := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .J2 ≃* ↥CFSG.Sporadic.J2.J :=
    CFSG.Sporadic.J2.nativeEquiv
  exact @CycOddPerm.of_equiv ↥CFSG.Sporadic.J2.J (CFSG.Blueprint.NativeSporadic.Carrier .J2) _ _
    _ _ e.symm cycOddPerm_j2Grp

theorem cycOddPerm_hsGrp :
    CycOddPerm ↥(J hsData) fun _ => False :=
  cycOddPerm_of_list hs_S_sylow (L := #[1, 15, 21, 3, 3]) hs_complete
    (fun j hj => by rw [hs_card_S]; exact hs_member_card j hj) (by decide) (N := 86625)
    (by norm_num [hs_card, hs_card_S]) (by norm_num)

theorem cycOddPerm_hs :
    CycOddPerm (CFSG.Blueprint.NativeSporadic.Carrier .HS) fun _ => False := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .HS ≃* ↥(J hsData) :=
    seedEquiv hs_facts.toBaseFacts
  exact @CycOddPerm.of_equiv ↥(J hsData) (CFSG.Blueprint.NativeSporadic.Carrier .HS) _ _ _ _
    e.symm cycOddPerm_hsGrp

theorem cycOddPerm_ruGrp :
    CycOddPerm ↥(J ruData) fun _ => False :=
  cycOddPerm_of_list ru_S_sylow (L := #[1, 15, 21, 3, 3]) ru_complete
    (fun j hj => by rw [ru_card_S]; exact ru_member_card j hj) (by decide) (N := 8906625)
    (by norm_num [ru_card, ru_card_S]) (by norm_num)

theorem cycOddPerm_ru :
    CycOddPerm (CFSG.Blueprint.NativeSporadic.Carrier .Ru) fun _ => False := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .Ru ≃* ↥(J ruData) :=
    seedEquiv ru_facts.toBaseFacts
  exact @CycOddPerm.of_equiv ↥(J ruData) (CFSG.Blueprint.NativeSporadic.Carrier .Ru) _ _ _ _
    e.symm cycOddPerm_ruGrp

end CFSG.Quasithin.H13.NQCat.T513P
