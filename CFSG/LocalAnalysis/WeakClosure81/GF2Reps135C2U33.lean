module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs
public import CFSG.Quasithin.H13.L32A753d
public import CFSG.LieType.Multipliers.ThreeThreeCenter
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)

theorem u33SmallModules_holds :
    U33SmallModules := by
  classical
  intro W _ _ hW L hq hirr hLM hrk
  have hq' : CFSG.Open.IsQuasisimple ↥L :=
    (CFSG.Quasithin.A3.isQuasisimple_iff_open).mp hq
  have hZ : Subgroup.center ↥L = ⊥ :=
    CFSG.LieType.Multipliers.center_eq_bot_of_lieModel_psu_three_three hq' hLM
  have hLM' : LieModel ↥L .PSU 3 3 1 :=
    LieModel.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans
        (QuotientGroup.quotientBot (G := ↥L))) hLM
  have hP : B42TypeU33 ↥L := ⟨hZ, hLM.statedClassicalModel (by decide)⟩
  have hirr' : ∀ U : Subgroup W, (∀ l ∈ L, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hirr.2.2.2 U hU bot_le le_top
  have hcard : Nat.card W ≤ 2 ^ 12 := by
    rw [w135_card_eq_two_pow_rk hW]
    exact Nat.pow_le_pow_right (by norm_num) hrk
  obtain ⟨-, hnat⟩ := CFSG.Quasithin.H13.L32A.M753.natural_of_irr hW hP hirr' hcard
  exact ⟨hLM', hnat⟩

end CFSG.LocalAnalysis.WeakClosure81
