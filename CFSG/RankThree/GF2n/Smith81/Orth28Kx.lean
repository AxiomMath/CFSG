module

public import CFSG.RankThree.GF2n.Smith81.Sec1Fusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

section Commutators

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

theorem centralizer_le_Kx (hs : Sit M Q Z X x) :
    Q ⊓ Subgroup.centralizer ({x} : Set G) ≤ Kx Q X := by
  intro c hc
  obtain ⟨hcQ, hcC⟩ := Subgroup.mem_inf.mp hc
  have hcomm : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  exact ⟨hcQ, Tim77.mem_normalizer_of_commute_of_isTI hs.X_isTI hs.mem hs.ne_one hcomm⟩

end Commutators

end CFSG.RankThree.GF2n.Smith81
