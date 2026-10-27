module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8Cases
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqOrb

public section

namespace CFSG.Quasithin.H13

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

namespace Lem1227Eq

theorem card_center_of_lieModel_psu {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q)
    (h : LieModel Q .PSU 3 3 1) : Nat.card Q = 6048 ∧ Subgroup.center Q = ⊥ := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ :=
    CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have hF9 : Nat.card F = 9 := by rw [hF]; norm_num
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsimple : IsSimpleGroup (StatedProj (StatedSU 3 (3 ^ 1) F)) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F 3 1 hF 3 le_rfl (by decide)
  have : IsSimpleGroup Q := e.isSimpleGroup
  have hbot :=
    CFSG.LinearGroups.UnitaryThreeOverNine.statedScalars_subgroupOf_statedSU_eq_bot hF9
  let e2 : StatedProj (StatedSU 3 3 F) ≃* ↥(StatedSU 3 3 F) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  let e3 : Q ≃* ↥(StatedSU 3 3 F) := e.trans e2
  refine ⟨?_, Lem8.center_eq_bot_of_isQuasisimple hq⟩
  rw [Nat.card_congr e3.toEquiv, CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hF9]

end Lem1227Eq

open Lem1227Eq

end CFSG.Quasithin.H13
