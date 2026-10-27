module

import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Toolkit
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem statedModel_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : StatedClassicalModel X .PSU 3 3 1) : StatedClassicalModel Y .PSU 3 3 1 :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem card_of_statedModel {X : Type} [Group X] (h : StatedClassicalModel X .PSU 3 3 1) :
    Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

theorem b42TypeU33_of_simple {X : Type} [Group X] (hs : IsSimpleGroup X)
    (h : StatedClassicalModel X .PSU 3 3 1) : B42TypeU33 X := by
  have hcard := card_of_statedModel h
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h1 | h1
    · exact h1
    · exfalso
      have hc : ∀ a b : X, a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top b) a)
      let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
      have := IsSimpleGroup.prime_card (α := X)
      rw [hcard] at this
      exact absurd this (by norm_num)
  refine ⟨hZ, statedModel_of_equiv ?_ h⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem b42TypeU33_toMulSub {L : Subgroup (GLV V)} (hs : IsSimpleGroup ↥L)
    (h : StatedClassicalModel ↥L .PSU 3 3 1) : B42TypeU33 ↥(toMulSub L) :=
  b42TypeU33_of_simple ((toMulSubEquiv L).symm.isSimpleGroup)
    (statedModel_of_equiv (toMulSubEquiv L) h)

end CFSG.Quasithin.G11.Harris.G2
