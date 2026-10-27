module

public import CFSG.Open.SporadicBabyMonsterRecognitionMilestoneDefs
import CFSG.Milestones.CL_LIT_Goldschmidt_strongly_closed_abelian
import CFSG.Monster.B.GSide.RecognitionExists
import CFSG.Monster.B.GSide.RecognitionFinal
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.cl_lit_stroth_leon_sims_baby_monster_recognition :
    ∃ (B : Type) (_ : Group B) (_ : Finite B), IsSimpleGroup B ∧
      Nat.card B = sporadicOrderBabyMonster ∧
      ∃ d₀ : B, orderOf d₀ = 2 ∧
        Nat.card (Subgroup.centralizer ({d₀} : Set B)) = 4 * sporadicOrderTwistedE6Two ∧
        ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
          ∀ d : G, orderOf d = 2 →
            Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
              Subgroup.centralizer ({d₀} : Set B)) →
            Nonempty (G ≃* B) :=
  CFSG.Monster.B.GSide.recognition_exists_of_models
    (CFSG.Monster.B.GSide.recognition_models_of_gold
      CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian)

end CFSG.Open

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.cl_lit_stroth_leon_sims_baby_monster_recognition_models
    (d₀ : Blueprint.NativeSporadic.B) (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (d : G) (hd : orderOf d = 2)
    (hcentralizer : Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
      Subgroup.centralizer ({d₀} : Set Blueprint.NativeSporadic.B))) :
    Nonempty (G ≃* Blueprint.NativeSporadic.B) :=
  CFSG.Monster.B.GSide.recognition_models_of_gold
    CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian d₀ hd₀ hrank G d hd hcentralizer

end CFSG.Open
