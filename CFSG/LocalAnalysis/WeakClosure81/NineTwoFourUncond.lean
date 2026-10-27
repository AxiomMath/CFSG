module

public import CFSG.LocalAnalysis.WeakClosure81.NineTwoF
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeDischarge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

variable {G : Type} [Group G] [Finite G] {V K S X : Subgroup G} {p : ℕ}


theorem nine_two_four_uncond (hV : Hyp7 V) (hm : 2 < rk ↥V) (h : Nine2Hyp V K S X p) :
    IsCyclic ↥X :=
  nine_two_four (sevenSixThreeAbelian_holds V) hV hm h

end CFSG.LocalAnalysis.WeakClosure81
