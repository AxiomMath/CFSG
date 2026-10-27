module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3319F
public import CFSG.Quasithin.Vol2.Ch3Sec3WLem3318M

public section

namespace CFSG.Quasithin.H13.L3319

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative

theorem stmt3_3_19_ofW
    (h14 : Stmt3_3_14) (hGA : CFSG.Open.GriessAllModelsStatement) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) (h12 : Step3_3_12R) (h15 : Step3_3_15R)
    (hC34 : CFSG.Quasithin.C134L32CorrM)
    (h20 : Stmt3_3_20) (h51 : AsB51) (hI16 : AsI16Cover) :
    Stmt3_3_19 := by
  intro G _ _ T M L D h
  refine ⟨fun e => ?_⟩
  have h18 := L3318.stmt3_3_18_ofW h14 hGA h38 h39 h12 h15 hC34 h20
  have hTL := L3318.le_normalizer_of_h14 h14 h
  obtain ⟨hVc, hB, hcase⟩ := Ln2.module_cases h18 h51 hI16 h h38 h39 hTL (Or.inr rfl) e
  rcases hcase with ⟨Z, -, -, hZ, hext⟩ | hsnd
  · rw [hZ rfl] at hext
    exact false_of_extSq h h38 h39 h12 h14 hGA h51 e hB hext
  · exact false_of_sumNatDual h h38 h39 h12 hGA h51 hTL e hB hsnd

end CFSG.Quasithin.H13.L3319
