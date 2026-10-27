module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.RankThree.PartTwo.Sec4

open Matrix CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem center_slPi_two_eq_bot {π : Bool} {f : ℕ} {F : Type} [Field F]
    (hK : PiField π 2 f F) : Subgroup.center ↥(slPi π 2 (2 ^ f) F) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite F := hK.finite
  cases π
  · have hcard : Nat.card F = (2 ^ f) ^ 2 := by rw [hK.card, piCard, Bool.cond_false]
    haveI : CharP F 2 := hK.charP
    obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := F) (r := 2) (f := f) hcard
    haveI : CharP (CFSG.LieType.Steinberg.fixedSubfield F 2 f) 2 := inferInstance
    change Subgroup.center ↥(StatedSU 2 (2 ^ f) F) = ⊥
    rw [← Subgroup.map_center_eq e, CFSG.Timmesfeld.RankOne.center_SL2_eq_bot,
      Subgroup.map_bot]
  · haveI : CharP F 2 := hK.charP
    change Subgroup.center ↥(StatedSL 2 F) = ⊥
    rw [← Subgroup.map_center_eq
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F),
      CFSG.Timmesfeld.RankOne.center_SL2_eq_bot, Subgroup.map_bot]

end CFSG.RankThree.PartTwo.Sec4

end
