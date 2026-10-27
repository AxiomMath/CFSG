module

public import CFSG.Quasithin.Vol2.Ch12Sec6L1f
public import CFSG.Quasithin.Vol2.Ch12Sec6L1e

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S126
open scoped IsMulCommutative

namespace S126L1g

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem part3 (h51 : AsB51) (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V) :
    thompsonJ T = thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) ∨
      (V ⊔ (reducedAggregate (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G))).relIndex
        (reducedAggregate (L ⊔ T)) ≤ 2 := by
  by_cases hJ : thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  · exact Or.inl (thompsonJ_eq_of_le (le_inf (thompsonJ_le_self T) hJ) inf_le_left)
  · right
    have hred := S126L1d.isTwoReducedIn_R2 L T
    have : IsMulCommutative ↥(reducedAggregate (L ⊔ T)) := hred.2.2.1.1
    exact S126L1f.relIndex_le_two F hH hH.hyp.irrPlus.1 (le_sup_left.trans hred.2.1)
      (S126L1e.inf_centralizer_le h1222 hH) (S126L1e.commutator_le_V h51 h1222 F hH hJ)

end S126L1g

theorem lemma12_6_1_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1228 : Stmt12_2_8)
    (h3228 : Stmt3_2_2_eight) (h51 : AsB51) : Lemma12_6_1 := by
  intro G _ _ T L V _ F hH
  exact ⟨S126L1a.part1 F, fun hZ => S126L1c.part2 h1222 hH hZ, S126L1g.part3 h51 h1222 F hH,
    S126L1b.part4 h331 h1222 h3228 F hH, S126L1a.part5 h1222 h1228 hH,
    fun hJ hZ => S126L1d.part6 h51 h1222 hH hJ hZ⟩

end CFSG.Quasithin.H13
