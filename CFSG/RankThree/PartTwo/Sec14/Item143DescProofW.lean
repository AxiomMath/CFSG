module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.GLS.Basic
public import CFSG.RankThree.PartTwo.Sec13.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem Desc143X.le_centralizer_of_isE27 {G : Type} [Group G] {A : Subgroup G}
    (hA : Late.IsE27 A) {a : G} (ha : a ∈ A) : A ≤ Subgroup.centralizer ({a} : Set G) :=
  fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨a, ha⟩))

end CFSG.RankThree.PartTwo.Sec14
