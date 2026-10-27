module

public import CFSG.RankThree.GF2n.Tim81Hyp4Bridge
public import CFSG.RankThree.GF2n.Tim81RootReduce

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

theorem comm_of_mem_conj_of_rootStep1 {g : G} (hgM : ¬ conjSubgroup g B ≤ M)
    (h1 : RootStep1 M B Q g) {x y s : G} (hx : x ∈ conjSubgroup g B ⊓ M) (hy : y ∈ Q)
    (hs : s ∈ conjSubgroup y (conjSubgroup g B ⊓ M)) : x * s = s * x :=
  H.toRootCore.comm_of_mem_conj_of_rootStep1 hgM h1 hx hy hs

end Hyp4

end CFSG.RankThree.GF2n.Tim78
