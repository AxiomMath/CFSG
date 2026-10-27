module

public import CFSG.Monster.Existence.Compat.Main
import CFSG.LieType.Simplicity.Exceptional
import CFSG.LieType.Steinberg.CentralExt.Model
import CFSG.Milestones.FAM_Th_simplicity
import CFSG.Monster.Existence.BabyOrder
import CFSG.Sporadic.Fi22.Simple
import CFSG.Sporadic.Fi23.Simple
import CFSG.Sporadic.McL.Simple
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Timmesfeld.Orders.Exceptional
public import Certificates.Certificate16012
public import CFSG.Sporadic.Th.KernelOrder

public section

namespace CFSG.Monster.Existence.Compat

open CFSG CFSG.Open CFSG.Blueprint

theorem card_nativeTh :
    Nat.card NativeSporadic.Th = monsterThOrder := by
  have hJ : Nat.card CFSG.Sporadic.Th.J = 90745943887872000 :=
    CFSG.Sporadic.Th.Kernel.card_J_eq CFSG.Sporadic.Th.th_kernel_facts
  rw [Nat.card_congr CFSG.Sporadic.Th.thEquivJ.toEquiv, hJ]
  exact Certificates.certificate16012.1

theorem chevalleyModel_of_lieModel {X : Type} [Group X]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (h : LieModel X t n p f) :
    ChevalleyExceptionalModel X t p f :=
  CFSG.Blueprint.LieModel.chevalleyExceptionalModel h ht

theorem card_u62_of_lieModel (X : Type) [Group X]
    (h : LieModel X .PSU 6 2 1) : Nat.card X = ordTwistedA 5 2 := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hf hK (by norm_num)]
  exact Certificates.certificate16012.2.1

theorem twoARemaining :
    TwoARemaining where
  b_card := CFSG.Monster.Existence.card_nativeB
  fi23_simple := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  fi23_card := CFSG.Sporadic.Fi23.card_Fi23.trans (by exact Certificates.certificate16012.2.2.1)
  th_simple := CFSG.Milestones.fam_th_simplicity
  th_card := card_nativeTh
  mcl_simple := CFSG.Sporadic.McL.isSimpleGroup_McL
  mcl_card := CFSG.Sporadic.McL.card_McL.trans (by exact Certificates.certificate16012.2.2.2.1)
  fi22_simple := CFSG.Sporadic.Fi22.isSimpleGroup_Fi22
  fi22_card := CFSG.Sporadic.Fi22.card_Fi22.trans (by exact Certificates.certificate16012.2.2.2.2)
  e6_simple X _ h :=
    (CFSG.LieType.Simplicity.fam_2e6_simplicity X 2 1 (chevalleyModel_of_lieModel (by decide) h)).2
  e6_card X _ h :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two (chevalleyModel_of_lieModel (by decide) h)
  f4_simple X _ h :=
    (CFSG.LieType.Simplicity.fam_f4_simplicity X 2 1 (chevalleyModel_of_lieModel (by decide) h)).2
  f4_card X _ h :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two (chevalleyModel_of_lieModel (by decide) h)
  u62_card := card_u62_of_lieModel

theorem compat_two
    (h : MonsterExistenceStatement MGriess) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G), IsSimpleGroup G ∧ Nat.card G = monsterOrder ∧
      ∃ a z : G, MonsterIsF1Type a z ∧ ¬ IsConj a z ∧
        (∀ t : G, orderOf t = 2 → IsConj a t ∨ IsConj z t) ∧ MonsterTwoAGraphData a z :=
  compat_two_of_canonical twoARemaining h

end CFSG.Monster.Existence.Compat
