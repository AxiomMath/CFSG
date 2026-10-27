module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Defs

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open scoped commutatorElement

@[expose] def Leaf_P9K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
    A2Cfg G T M L D H K q →
      ∃ a x : G, a ∈ K ∧ a ^ 2 ∈ pCoreOf 2 K ∧ a ∉ pCoreOf 2 K ∧
        x ∈ oTwoUpper H ∧ x ∈ K ∧ orderOf x = 3 ∧ ⁅x, a⁆ ∈ pCoreOf 2 K ∧
        pCoreOf 2 K ≤ a2R H ∧
        ∀ w ∈ K, ⁅w, a⁆ ∈ pCoreOf 2 K → w ∈ Subgroup.normalizer (a2R H : Set G)

end CFSG.Quasithin.H13.NFa2
