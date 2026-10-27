module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctComb
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctIntC

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree.ReeTag


theorem octIntFacts : OctIntFacts octS where
  mem_S _ _ _ := Iff.rfl
  isRoot _ h1 h8 := octPos_isRoot h1 h8
  closed _ _ h1 hij h8 _ hα _ hβ _ _ ha hb hr := octS_closed h1 hij h8 hα hβ ha hb hr
  ideal_left _ _ h2 hij h8 _ hα _ hβ _ _ ha hb hr := octS_ideal_left h2 hij h8 hα hβ ha hb hr
  ideal_right _ _ h1 hij h7 _ hα _ hβ _ _ ha hb hr := octS_ideal_right h1 hij h7 hα hβ ha hb hr
  disjoint _ _ h1 h8 h1' h8' hne := octPos_disjoint h1 h8 h1' h8' hne
  posBlock _ h1 h8 := octPos_mem_posBlocks h1 h8
  one_eight := octS_one_eight


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem octCarrier : OctCarrier K a :=
  octCarrier_of octIntFacts

theorem octUnique : OctUnique K a :=
  octUnique_of octIntFacts

theorem octRev : OctRev K a :=
  octRev_of octIntFacts

theorem octSub : OctSub K a :=
  octSub_of octIntFacts

end CFSG.Quasithin.H13.F431.TwoF4
