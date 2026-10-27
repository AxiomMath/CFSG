module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LK2Torus
import CFSG.LocalAnalysis.UniquenessCase.Lie.SL4Datum

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing)

variable {G : Type} [Group G] [Finite G]

theorem s21_14R3LK2_dataOfSetup (hGA : CFSG.Open.GriessAllModelsStatement) (hS : Standing G)
    (hUC : CFSG.Open.rankThreeUC G) (S : Setup G)
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)) :
    S21_14R3LK2 (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True) :=
  s21_14R3LK2_dataOfSetup_of_datum (fun _ _ _ _ _ hK => uc22pwr1_datum_sl4 hK) hGA hS hUC S h211

end CFSG.LocalAnalysis.UniquenessCase.UC22
