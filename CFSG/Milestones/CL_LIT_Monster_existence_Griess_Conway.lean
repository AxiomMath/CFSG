module

public import CFSG.Monster.Existence.Defs
import CFSG.Monster.Existence.Compat.OneStroth
import CFSG.Monster.Existence.MilestoneTableOne
import CFSG.Milestones.CL_LIT_Stroth_Leon_Sims_Baby_Monster_recognition
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.cl_lit_monster_existence_griess_conway_1 :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), IsSimpleGroup G ∧ Nat.card G = monsterOrder ∧
      ∃ a z : G, MonsterIsF1Type a z ∧ ¬ IsConj a z ∧
        ∀ t : G, orderOf t = 2 → IsConj a t ∨ IsConj z t :=
  CFSG.Monster.Existence.Compat.compat_one_of_stroth
    fun d₀ hd₀ hrank G _ _ _ d hd hc =>
      CFSG.Milestones.cl_lit_stroth_leon_sims_baby_monster_recognition_models d₀ hd₀ hrank G d hd hc

end CFSG.Open

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.cl_lit_monster_existence_griess_conway_2 :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), IsSimpleGroup G ∧ Nat.card G = monsterOrder ∧
      ∃ a z : G, MonsterIsF1Type a z ∧ ¬ IsConj a z ∧
        (∀ t : G, orderOf t = 2 → IsConj a t ∨ IsConj z t) ∧ MonsterTwoAGraphData a z :=
  CFSG.Monster.Existence.Compat.compat_two
    (CFSG.Monster.Existence.monsterExistenceStatement_MGriess_of_recognition
      fun d₀ hd₀ hrank G _ _ _ d hd hc =>
        CFSG.Milestones.cl_lit_stroth_leon_sims_baby_monster_recognition_models d₀ hd₀ hrank G d hd
          hc)

end CFSG.Open

namespace CFSG.Milestones

open CFSG.Monster.Existence in
theorem cl_lit_monster_existence_griess_conway :
    MonsterExistenceStatement MGriess :=
  monsterExistenceStatement_MGriess_of_recognition fun d₀ hd₀ hrank G _ _ _ d hd hc =>
    cl_lit_stroth_leon_sims_baby_monster_recognition_models d₀ hd₀ hrank G d hd hc

end CFSG.Milestones
