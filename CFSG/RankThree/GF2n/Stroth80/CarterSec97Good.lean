module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec9RStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

theorem LB_conjSubgroup (M Q B : Subgroup G) {g : G}
    (hQ : ∀ m ∈ M, conjSubgroup m Q = Q) (hg : g ∈ M) :
    LB M Q (conjSubgroup g B) = conjSubgroup g (LB M Q B) := by
  unfold LB
  have hM : conjSubgroup g M = M :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hg)
  rw [QB_conj, conjSubgroup_sup', conjSubgroup_inf, hQ g hg, hM]

theorem HS9.goodPt_conj_of_mem (M Q B Y : Subgroup G) {g : G}
    (hQ : ∀ m ∈ M, conjSubgroup m Q = Q) (hg : g ∈ M)
    (hY : conjSubgroup g Y = Y) :
    HS9.GoodPt M Q B Y (conjSubgroup g B) :=
  ⟨g, hg, hY, (LB_conjSubgroup M Q B hQ hg).symm⟩

end CFSG.RankThree.GF2n.Stroth80
