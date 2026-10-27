module

public import CFSG.RankThree.PartOne.CTP.SeitzFine
public import CFSG.RankThree.PartOne.SEITZ2.G2Outer
public import CFSG.RankThree.PartOne.SEITZ2.D4Outer
public import CFSG.RankThree.PartOne.SEITZ2.SzOuter
public import CFSG.RankThree.PartOne.SEITZ2.ReeOuter

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open CFSG.RankThree.PartOne.CTP

section


theorem fieldAutG2_of_pair (h : SubfieldPairG2) : FieldAutG2 :=
  fun _ hq _ => extSeitzAtOuter_G2_of_pair h hq

theorem fieldAut3D4_of_pair (h : SubfieldPairD4) : FieldAut3D4 :=
  fun _ hq _ => extSeitzAtOuter_trialityD4_of_pair h hq

theorem fieldAut2F4_of_pair (h : SubfieldPairReeF4) : FieldAut2F4 :=
  fun m _ => extSeitzAtOuter_reeF4_of_pair h m

end

theorem fieldAutSz_of_pair (h : SubfieldPairSz) : FieldAutSz :=
  fun m _ => extSeitzAtOuter_suzuki_of_pair h m

section Fine


theorem seitzFieldAutFine_of_pairs (h : SubfieldPairSU 3 ∧ SubfieldPairSU 4 ∧ SubfieldPairSU 5 ∧
    SubfieldPairSp 2 ∧ SubfieldPairSp 3 ∧ FieldAutOmega8m ∧ SubfieldPairG2 ∧ SubfieldPairD4 ∧
    SubfieldPairSz ∧ SubfieldPairReeF4) : SeitzFieldAutFine := by
  obtain ⟨hSU3, hSU4, hSU5, hSp2, hSp3, hOm, hG2, h3D4, hSz, h2F4⟩ := h
  exact ⟨hSU3, hSU4, hSU5, hSp2, hSp3, hOm, fieldAutG2_of_pair hG2, fieldAut3D4_of_pair h3D4,
    fieldAutSz_of_pair hSz, fieldAut2F4_of_pair h2F4⟩

end Fine

end CFSG.RankThree.PartOne.SEITZ2
