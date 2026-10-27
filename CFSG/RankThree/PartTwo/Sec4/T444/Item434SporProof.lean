module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporJ1
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporM11
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporRank
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporONan
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporRankTwo

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

section Families


@[expose] def Item434Spor_M12_9 : Prop :=
  Item434SporAtCard .M12 9

@[expose] def Item434Spor_M22_9 : Prop :=
  Item434SporAtCard .M22 9

@[expose] def Item434Spor_M23_9 : Prop :=
  Item434SporAtCard .M23 9

@[expose] def Item434Spor_M24_9 : Prop :=
  Item434SporAtCard .M24 9

@[expose] def Item434Spor_J2_9 : Prop :=
  Item434SporAtCard .J2 9

@[expose] def Item434Spor_HS_9 : Prop :=
  Item434SporAtCard .HS 9

@[expose] def Item434Spor_J4_9 : Prop :=
  Item434SporAtCard .J4 9

@[expose] def Item434Spor_He_9 : Prop :=
  Item434SporAtCard .He 9

@[expose] def Item434Spor_Ru_9 : Prop :=
  Item434SporAtCard .Ru 9

@[expose] def Item434Spor_J3_9Cover : Prop :=
  Item434SporAtNineCover .J3

@[expose] def Item434Spor_McL_9Cover : Prop :=
  Item434SporAtNineCover .McL

@[expose] def Item434Spor_ONan_9Cover : Prop :=
  Item434SporAtNineCover .ONan

@[expose] def Item434Spor_J3_27 : Prop :=
  Item434SporAtCard .J3 27

@[expose] def Item434Spor_McL_27 : Prop :=
  Item434SporAtCard .McL 27

@[expose] def Item434Spor_Ly_27 : Prop :=
  Item434SporAtCard .Ly 27

@[expose] def Item434Spor_Suz_27 : Prop :=
  Item434SporAtCard .Suz 27

@[expose] def Item434Spor_Co3_27 : Prop :=
  Item434SporAtCard .Co3 27

@[expose] def Item434Spor_Co2_27 : Prop :=
  Item434SporAtCard .Co2 27

@[expose] def Item434Spor_HN_27 : Prop :=
  Item434SporAtCard .HN 27

@[expose] def Item434Spor_Th_27 : Prop :=
  Item434SporAtCard .Th 27

theorem item434Spor_of_remainder
    (hM12 : Item434Spor_M12_9) (hM22 : Item434Spor_M22_9) (hM23 : Item434Spor_M23_9)
    (hM24 : Item434Spor_M24_9) (hJ2 : Item434Spor_J2_9) (hHS : Item434Spor_HS_9)
    (hJ4 : Item434Spor_J4_9) (hHe : Item434Spor_He_9) (hRu : Item434Spor_Ru_9)
    (hJ3c : Item434Spor_J3_9Cover) (hMcLc : Item434Spor_McL_9Cover)
    (hONc : Item434Spor_ONan_9Cover) (hJ3 : Item434Spor_J3_27) (hMcL : Item434Spor_McL_27)
    (hLy : Item434Spor_Ly_27) (hSuz : Item434Spor_Suz_27) (hCo3 : Item434Spor_Co3_27)
    (hCo2 : Item434Spor_Co2_27) (hHN : Item434Spor_HN_27) (hTh : Item434Spor_Th_27) :
    Item434Spor := by
  refine item434Spor_of_split fun s hs => ?_
  simp only [sporadics42, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact item434SporM11
  · exact item434SporAt_of_card hM12 item434SporAtCard_m12_27
  · exact item434SporAt_of_card hM22 item434SporAtCard_m22_27
  · exact item434SporAt_of_card hM23 item434SporAtCard_m23_27
  · exact item434SporAt_of_card hM24 item434SporAtCard_m24_27
  · exact item434SporJ1
  · exact item434SporAt_of_card hJ2 item434SporAtCard_j2_27
  · exact item434SporAt_of_card (item434SporAtCard_j3_nine_of hJ3c) hJ3
  · exact item434SporAt_of_card hJ4 item434SporAtCard_j4_27
  · exact item434SporAt_of_card (item434SporAtCard_mcl_nine_of hMcLc) hMcL
  · exact item434SporAt_of_card item434SporAtCard_ly_nine hLy
  · exact item434SporAt_of_card hHS item434SporAtCard_hs_27
  · exact item434SporAt_of_card hHe item434SporAtCard_he_27
  · exact item434SporAt_of_card item434SporAtCard_suz_nine hSuz
  · exact item434SporAt_of_card hRu item434SporAtCard_ru_27
  · exact item434SporAt_of_card (item434SporAtCard_onan_nine_of hONc) item434SporAtCard_onan_27
  · exact item434SporAt_of_card item434SporAtCard_co3_nine hCo3
  · exact item434SporAt_of_card item434SporAtCard_co2_nine hCo2
  · exact item434SporAt_of_card item434SporAtCard_hn_nine hHN
  · exact item434SporAt_of_card item434SporAtCard_th_nine hTh

end Families

end CFSG.RankThree.PartTwo.Sec4
