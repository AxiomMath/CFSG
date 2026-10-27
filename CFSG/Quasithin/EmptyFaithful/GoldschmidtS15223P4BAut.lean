module

public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223P4

namespace B

section Stars

variable {G : Type} [Group G]

theorem mem_autOn_iff' {X V : Subgroup G} {a : MulAut ↥V} :
    a ∈ autOn X V ↔ ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ X ∧ conjAct V g = a := by
  unfold autOn
  rw [Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

theorem conjAct_eq_one_iff' (V : Subgroup G) (g : ↥(Subgroup.normalizer (V : Set G))) :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

theorem conjAct_mem_normalizer_autOn {Y V : Subgroup G} (g : ↥(Subgroup.normalizer (V : Set G)))
    (hgY : (g : G) ∈ Subgroup.normalizer (Y : Set G)) :
    conjAct V g ∈ Subgroup.normalizer (autOn Y V : Set (MulAut ↥V)) :=
  CFSG.Quasithin.AutOn.conjAct_mem_normalizer_autOn g hgY

theorem autOn_eq_bot_of_le_centralizer {X V : Subgroup G}
    (h : X ≤ Subgroup.centralizer (V : Set G)) : autOn X V = ⊥ :=
  CFSG.Quasithin.AutOn.autOn_eq_bot_of_le_centralizer h

end Stars

end B

end S15223P4

end CFSG.Quasithin
