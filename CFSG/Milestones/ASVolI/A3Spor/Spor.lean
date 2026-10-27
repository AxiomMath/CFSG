module

public import CFSG.Milestones.ASVolI.A3Spor.List
public import CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHS
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312J2Model
public import CFSG.Sporadic.J2
import all CFSG.Blueprint.NativeSporadic
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHS
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu

public section

namespace CFSG.ASVolI

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Sporadic.SmallF2

theorem burnsideA315s_noConfig_M12 :
    ∀ S B : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .M12),
      ¬ burnsideA315x_Config (CFSG.Blueprint.NativeSporadic.Carrier .M12) S B :=
  burnsideA315s_false_of_indexThree (Γ := ↥CFSG.Blueprint.NativeSporadic.M12)
    CFSG.Quasithin.H.MathieuLat.m12_indexThree

theorem burnsideA315s_noConfig_M24 :
    ∀ S B : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .M24),
      ¬ burnsideA315x_Config (CFSG.Blueprint.NativeSporadic.Carrier .M24) S B :=
  burnsideA315s_false_of_indexThree (Γ := ↥CFSG.Blueprint.NativeSporadic.M24)
    CFSG.Quasithin.H.MathieuLat.m24_indexThree

theorem burnsideA315s_noConfig_J2Grp :
    ∀ S B : Subgroup ↥CFSG.Sporadic.J2.J, ¬ burnsideA315x_Config ↥CFSG.Sporadic.J2.J S B := by
  have hS : Nat.card ↥CFSG.Quasithin.A312J2.j2CtxA.S = 2 ^ 7 :=
    CFSG.Quasithin.H13.NQCat.T513P.card_of_isSylowTwoOf_top CFSG.Quasithin.A312J2.j2A_sylow
      (m := 4725) (by rw [CFSG.Sporadic.J2.card_J]; norm_num) (by decide)
  exact burnsideA315s_false_of_list CFSG.Quasithin.A312J2.j2A_sylow
    (CFSG.Quasithin.E2P.SporB.lat_all _ CFSG.Quasithin.A312J2.j2A_hL)
    (fun j hj => by rw [hS]; exact CFSG.Quasithin.A312J2.j2A_card hj) (by decide) (N := 4725)
    (by rw [CFSG.Sporadic.J2.card_J, hS]; norm_num) (by norm_num)

theorem burnsideA315s_noConfig_J2 :
    ∀ S B : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .J2),
      ¬ burnsideA315x_Config (CFSG.Blueprint.NativeSporadic.Carrier .J2) S B := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .J2 ≃* ↥CFSG.Sporadic.J2.J :=
    CFSG.Sporadic.J2.nativeEquiv
  exact @burnsideA315s_noConfig_of_equiv (CFSG.Blueprint.NativeSporadic.Carrier .J2)
    ↥CFSG.Sporadic.J2.J _ _ e burnsideA315s_noConfig_J2Grp

open CFSG.QuasithinUnique.Ch1.SporLat.HS in
open CFSG.Sporadic.HS.Native (hsData) in
theorem burnsideA315s_noConfig_HS :
    ∀ S B : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .HS),
      ¬ burnsideA315x_Config (CFSG.Blueprint.NativeSporadic.Carrier .HS) S B := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .HS ≃* ↥(J hsData) :=
    seedEquiv hs_facts.toBaseFacts
  have h : ∀ S B : Subgroup ↥(J hsData), ¬ burnsideA315x_Config ↥(J hsData) S B :=
    burnsideA315s_false_of_list hs_S_sylow (L := #[1, 15, 21, 3, 3]) hs_complete
      (fun j hj => by rw [hs_card_S]; exact hs_member_card j hj) (by decide) (N := 86625)
      (by norm_num [hs_card, hs_card_S]) (by norm_num)
  exact @burnsideA315s_noConfig_of_equiv (CFSG.Blueprint.NativeSporadic.Carrier .HS)
    ↥(J hsData) _ _ e h

open CFSG.QuasithinUnique.Ch1.SporLat.Ru in
open CFSG.Sporadic.Ru.Native (ruData) in
theorem burnsideA315s_noConfig_Ru :
    ∀ S B : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Ru),
      ¬ burnsideA315x_Config (CFSG.Blueprint.NativeSporadic.Carrier .Ru) S B := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .Ru ≃* ↥(J ruData) :=
    seedEquiv ru_facts.toBaseFacts
  have h : ∀ S B : Subgroup ↥(J ruData), ¬ burnsideA315x_Config ↥(J ruData) S B :=
    burnsideA315s_false_of_list ru_S_sylow (L := #[1, 15, 21, 3, 3]) ru_complete
      (fun j hj => by rw [ru_card_S]; exact ru_member_card j hj) (by decide) (N := 8906625)
      (by norm_num [ru_card, ru_card_S]) (by norm_num)
  exact @burnsideA315s_noConfig_of_equiv (CFSG.Blueprint.NativeSporadic.Carrier .Ru)
    ↥(J ruData) _ _ e h

open CFSG.QuasithinUnique.Ch1.SporLat.He in
theorem burnsideA315s_noConfig_He :
    ∀ S B : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .He),
      ¬ burnsideA315x_Config (CFSG.Blueprint.NativeSporadic.Carrier .He) S B := by
  have e : CFSG.Blueprint.NativeSporadic.Carrier .He ≃* ↥CFSG.Sporadic.He.J :=
    CFSG.Sporadic.He.heEquivJ
  have h : ∀ S B : Subgroup ↥CFSG.Sporadic.He.J, ¬ burnsideA315x_Config ↥CFSG.Sporadic.He.J S B :=
    burnsideA315s_false_of_list he_S_sylow (L := #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3])
      he_complete (fun j hj => by rw [he_card_S]; exact he_member_card j hj) (by decide)
      (N := 3935925) (by rw [he_card, he_card_S]; ring) (by norm_num)
  exact @burnsideA315s_noConfig_of_equiv (CFSG.Blueprint.NativeSporadic.Carrier .He)
    ↥CFSG.Sporadic.He.J _ _ e h

end CFSG.ASVolI
