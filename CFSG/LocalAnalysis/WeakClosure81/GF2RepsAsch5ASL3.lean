module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IC
public import CFSG.Quasithin.EmptyFaithful.A38c15IrrClose
public import CFSG.Quasithin.Vol2.Ch11SecU1L33I
public import CFSG.Quasithin.Vol2.Ch11SecU1U3O
public import CFSG.Quasithin.Vol2.Ch11SecU1U3R

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11

variable {G : Type} [Group G] [Finite G]

section L3


theorem nParam_le_one_of_isPSL3_noSQ {T : Subgroup G}
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp4 : p % 4 = 3) (hP : IsPSL 3 p 1 ↥(CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  by_cases hTL : T ≤ CFSG.generalizedFitting G
  · exact SecU1.L3I.nParam_le_one_of_psl3_inner hp hp2 hP hTL hFT
  · by_cases hp3 : p = 3
    · subst hp3
      exact SecU1.L33.nParam_le_one_of_psl3_three A38c15.sl3OddIrr hFs hP hT.1 hFT hTL
    · have hp7 : 7 ≤ p := by
        have := hp.two_le
        omega
      exact SecU1.L3I.nParam_le_one_of_psl3_outer A38c15.sl3OddIrr hp hp7 hp4 hFs hP hT.1 hFT hTL

end L3

section U3


theorem nParam_le_one_of_isPSU3_noSQ {T : Subgroup G}
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hP : IsPSU 3 p 1 ↥(CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hp5 : p = 5
  · subst hp5
    exact SecU1.U3.nParam_le_one_of_psu3_five hP hFs hT hFT
  · exact SecU1.U3.nParam_le_one_of_psu3_of_ne_five hp5 hp4 hP hFs hT hFT

end U3

end CFSG.LocalAnalysis.WeakClosure81

end
