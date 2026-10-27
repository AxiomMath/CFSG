module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieC
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieB

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.Sec53F.Unit

section Hyp

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem stdTwo_Y (hf : 2 ≤ f) :
    Lift.StdTwo (hypPSU h 2 1) (hypProjUnitriangular h 2 1) (u5PtP h) (u5LnP h) (z5Y h)
      (t5Y h) where
  z_mem := z5Y_mem_U
  t_mem := t5Y_mem_U
  z_two := orderOf_z5Y
  t_two := orderOf_t5Y
  cls _ hx := cls_Y hf hx
  noconj φ := noconj_Y φ
  center _ hw hc hw1 := center_Y hw hc hw1
  aut_z _ h1 h2 := aut_z_Y h1 h2
  aut_t _ h1 h2 := aut_t_Y h1 h2
  cent_z := Or.inl cent_z_Y
  cent_t := Or.inr cent_t_Y

end Hyp

end CFSG.Quasithin.H13.F431.Un
