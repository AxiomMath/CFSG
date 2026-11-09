module

public import Certificates.Data.Kernel.Census.CatFacts.C2009Defs

public section

set_option maxHeartbeats 0

namespace CFSG.Certificates.Kernel.CatFacts

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Certificates.Kernel.PkEnum

theorem lQQ_eq : mkLv lQQN = lv0 QQ45 := by decide +kernel

theorem lQH_eq : mkLv lQHN = lv0 cfQH := by decide +kernel

theorem lQR_eq : mkLv lQRN = lv0 cfQR := by decide +kernel

theorem lQE_eq : mkLv lQEN = lv0 cfQE := by decide +kernel

theorem lQP_eq : mkLv lQPN = lv0 QP45 := by decide +kernel

theorem lQA_eq : lQAL = lv0 QA45 := by decide +kernel

theorem tAL_eq : tAL = transL QA45 := by decide +kernel

theorem siftP_QP45 (σ : Equiv.Perm (Fin 45)) : siftP QP45 σ 0 = siftPQ σ := by
  rw [siftPQ, lQP_eq]
  rfl

theorem siftP_QA45 (σ : Equiv.Perm (Fin 45)) : siftP QA45 σ 0 = siftAQ σ := by
  rw [siftAQ, lQA_eq]
  rfl

theorem tP_eq : ((mkLv lQPN).map fun l => transV l.2) = transL QP45 := by
  rw [lQP_eq]
  simp only [lv0, levelsV, transL, List.drop_zero, List.map_map, Function.comp_def]

theorem cA1_eq : cA1 = cA0 := by
  unfold cA1
  rw [lQQ_eq, lQH_eq, lQR_eq, lQE_eq, tP_eq, lQP_eq, tAL_eq]
  rfl

end CFSG.Certificates.Kernel.CatFacts
