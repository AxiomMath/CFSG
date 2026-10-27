module

public import CFSG.Quasithin.Vol2.GoldschmidtCh7NormalRows
public import CFSG.Quasithin.Vol2.GoldschmidtCh7NormalLie
public import CFSG.Quasithin.Vol2.GoldschmidtCh7NormalMathieu
public import CFSG.Quasithin.Vol2.Ch7Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtCh7NormalAct

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

theorem stmt7_1_1_normal_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hD : ModelDichotomies) :
    Stmt7_1_1_normal := by
  intro G _ _ T L I hyp hab hrow
  by_contra hnot
  obtain ⟨t, htT, htL⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  exact false_of_not_normalizes hyp.fsu h37 h38 htT htL (hmodel_of_row hD hrow)

theorem modelDichotomies_of :
    ModelDichotomies where
  su3 := fun _ K _ _ hn hK => normalDichotomy_statedSU_three hn K hK
  sz := fun _ K _ _ ha hK => normalDichotomy_suzukiGroup ha K hK
  sl3 := fun _ K _ _ _ => normalDichotomy_statedSL_three K
  sp4 := fun _ K _ _ hn hK => normalDichotomy_statedSp_two hn K hK
  alt6 := normalDichotomy_alternatingGroup (by norm_num)
  alt7 := normalDichotomy_alternatingGroup (by norm_num)
  m24 := normalDichotomy_autPerm
  m23 := fun x => normalDichotomy_stab_m23 x
  m22 := fun _ _ hxy => normalDichotomy_stab_m22 hxy
  m12 := fun _ heY hw => normalDichotomy_m24Fix heY hw

theorem stmt7_1_1_normal_holds
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Stmt7_1_1_normal :=
  stmt7_1_1_normal_of h37 h38 modelDichotomies_of

end CFSG.Quasithin.H13
