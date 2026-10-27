module

public import CFSG.Quasithin.Background.AutOnBasics

public section

namespace CFSG.Quasithin.AutOn

open CFSG.Open

variable {G : Type*} [Group G]

theorem ker_conjAct (V : Subgroup G) :
    (conjAct V).ker = (Subgroup.centralizer (V : Set G)).subgroupOf
      (Subgroup.normalizer (V : Set G)) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, conjAct_eq_one_iff]

theorem card_autOn_eq_relIndex_centralizer {A V : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (autOn A V) = (Subgroup.centralizer (V : Set G)).relIndex A := by
  unfold autOn
  rw [← Subgroup.relIndex_ker, ker_conjAct, Subgroup.relIndex_subgroupOf hA]

theorem card_autOn_eq_relIndex {A V : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (autOn A V) = (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A := by
  rw [card_autOn_eq_relIndex_centralizer hA, Subgroup.inf_relIndex_left]

end CFSG.Quasithin.AutOn
