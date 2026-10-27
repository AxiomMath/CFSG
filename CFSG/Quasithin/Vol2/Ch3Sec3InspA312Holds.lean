module

public import CFSG.Quasithin.Vol2.Ch3Sec3InspA312Excl
public import CFSG.Quasithin.Vol2.Ch3Sec3FactAutL3Holds
public import CFSG.Quasithin.Vol2.KGFactAutSylowL2Sq
public import CFSG.Quasithin.Vol2.KGFactAutSylowM11
public import CFSG.Quasithin.Vol2.KGFactAutSylowM22
public import CFSG.Quasithin.Vol2.KGFactAutSylowM23
public import CFSG.Quasithin.Vol2.KGFactAutSylowJ4

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Quasithin InspA312

theorem inspA312F618_of (hK : KGInputs) (hE : ExclInputs) : InspA312F618 := by
  intro Q _ _ B L hBL hlist hC
  rcases hlist with rfl | hcase | hnq
  · exact Or.inl (sup_eq_left.mpr (solvRad_le _))
  · rcases hcase with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · exact (false_of_c2 hE hC h).elim
    · exact (false_of_c3 hE hC h).elim
    · exact Or.inr (radQuot_of_c4 hK h)
    · exact Or.inr (radQuot_of_c5 hK h)
    · exact Or.inr (radQuot_of_c6 hK h)
    · exact Or.inr (radQuot_of_c7 hK h)
    · rcases h with ⟨p, hp, hp3, -, hL⟩ | ⟨hB, -⟩
      · exact Or.inr (radQuot_of_c8_left hK hp hp3 hL)
      · exact (false_of_c8_right hE hC hB).elim
    · exact Or.inr (radQuot_of_c9 hK h)
    · exact Or.inr (radQuot_of_c10 hK h)
    · exact Or.inr (radQuot_of_c11 hK h)
    · exact Or.inr (radQuot_of_c12 hK h)
    · exact Or.inr (radQuot_of_c13 hK h)
    · exact Or.inr (radQuot_of_c14 hK h)
    · exact (false_of_c15 hE hC h).elim
    · exact (false_of_c16 hE hC h).elim
    · exact Or.inr (radQuot_of_c17 hK h)
    · exact Or.inr (radQuot_of_c18 hK h)
    · exact Or.inr (radQuot_of_c19 hK h)
    · exact Or.inr (radQuot_of_c20 hK h)
  · rcases hnq with ⟨-, hL, -⟩ | ⟨-, -, N, hN, hNeq, hSL⟩
    · refine Or.inl (le_antisymm (sup_le hBL (solvRad_le L)) ?_)
      have hOO : ((CFSG.oddCore ↥L).map L.subtype).subgroupOf L = CFSG.oddCore ↥L :=
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
      have hOL : (CFSG.oddCore ↥L).map L.subtype ≤ solvRad L :=
        le_solvRad (Subgroup.map_subtype_le _) (by rw [hOO]; infer_instance)
          isSolvable_oddCore_map
      calc L = B ⊔ (CFSG.oddCore ↥L).map L.subtype := hL
        _ ≤ B ⊔ solvRad L := sup_le_sup_left hOL B
    · exact (false_of_sup_quotient hE hC (le_normalizer_oddCore hBL) isSolvable_oddCore_map hNeq
        hSL).elim

theorem sporSimple_of {s : TauCeti.SporadicName}
    (h : Finite (CFSG.Blueprint.NativeSporadic.Carrier s) ∧
      Nontrivial (CFSG.Blueprint.NativeSporadic.Carrier s) ∧
      IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier s))
    (hp : ¬ (Nat.card (CFSG.Blueprint.NativeSporadic.Carrier s)).Prime) : SporSimple s :=
  have := h.1
  ⟨h.2.2, CFSG.Quasithin.A314.exists_noncomm_of_simple h.2.2 hp⟩

theorem kgInputs_holds :
    KGInputs where
  l42 := KGAutSyl.factAutSylowL42_holds
  l52 := KGAutSyl.factAutSylowL52_holds
  a7 := KGAutSyl.factAutSylowA7_holds
  l2sq := KGAutSyl.factAutSylowL2Sq_holds
  l3eps := factAutL3Eps_holds
  m11 := KGAutSyl.factAutSylowM11_holds
  m22 := KGAutSyl.factAutSylowM22_holds
  m23 := KGAutSyl.factAutSylowM23_holds
  m24 := KGAutSyl.factAutSylowM24_holds
  j4 := KGAutSyl.factAutSylowJ4_holds
  hs := KGAutSyl.factAutSylowHS_holds
  ru := KGAutSyl.factAutSylowRu_holds
  he := KGHe.factAutHeSylow_holds
  sM11 := sporSimple_of CFSG.Sporadic.Mathieu.fam_m11_simplicity (by
    rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M11) = _ from
      CFSG.Sporadic.Mathieu.card_M11]
    norm_num)
  sM22 := sporSimple_of CFSG.Sporadic.Mathieu.fam_m22_simplicity (by
    rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = _ from
      CFSG.Sporadic.Mathieu.card_M22]
    norm_num)
  sM23 := sporSimple_of CFSG.Sporadic.Mathieu.fam_m23_simplicity (by
    rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M23) = _ from
      CFSG.Sporadic.Schreier.m23_card]
    norm_num)
  sM24 := sporSimple_of CFSG.Sporadic.Mathieu.fam_m24_simplicity (by
    rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = _ from
      CFSG.Sporadic.Mathieu.card_M24]
    norm_num)
  sJ4 := sporSimple_of CFSG.Sporadic.J4.fam_j4_simplicity (by
    rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .J4) = _ from
      CFSG.Sporadic.J4.card_J4]
    norm_num)
  sHS := sporSimple_of CFSG.Sporadic.HS.fam_hs_simplicity (by
    rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .HS) = _ from
      CFSG.Sporadic.HS.card_HS]
    norm_num)
  sHe := sporSimple_of CFSG.Sporadic.He.fam_he_simplicity (by
    rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) = _ from
      CFSG.Sporadic.He.card_He]
    norm_num)
  sRu := sporSimple_of CFSG.Sporadic.Ru.fam_ru_simplicity (by
    rw [show Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Ru) = _ from
      CFSG.Sporadic.Ru.card_Ru]
    norm_num)

theorem exclInputs_holds :
    ExclInputs :=
  ⟨CFSG.Sporadic.Mathieu.card_M12, fun _ _ _ h => F134.not_three_dvd_card_of_suzukiModel h⟩

theorem inspA312F618_holds :
    InspA312F618 :=
  inspA312F618_of kgInputs_holds exclInputs_holds

end CFSG.Quasithin.H13
