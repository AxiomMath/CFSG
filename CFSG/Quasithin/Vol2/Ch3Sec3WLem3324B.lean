module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324C2
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324C3
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324
public import CFSG.Quasithin.Vol2.Ch3Sec3WLem3323C4Fix

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

theorem step3_3_24_ofW
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14)
    (hC34 : CFSG.Quasithin.C134L32CorrM)
    (h20 : Stmt3_3_20) : Step3_3_24 := by
  intro G _ _ T M L D h hP hk2 _ hD
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  obtain ⟨α, hα, -⟩ := Mod3323.exists_modO2Surj h hTL hP
  have hMS : IsMSPair (L ⊔ T) T :=
    h.isMSPair h38 h39 (CFSG.Quasithin.S1567.isRankTwoLie2Derived_of_modO2 α hα.1 hα.2) hTL
  obtain ⟨i, hi⟩ := hC34 G (L ⊔ T) T L hMS h.toSetup331.mem_cComp
    (Subgroup.coe_mul_of_right_le_normalizer_left L T hTL)
    ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩
  match i, hi with
  | 0, hi => exact hi.elim
  | 1, hi =>
    exact Lem3328.not_hasNoncentralTwoChief_two_of_isShort2
      (One3323.isLnBlock_of_isSL3Block hi.1 hα).1 hk2
  | 2, hi => exact C2of3324.false_case2 h38 h39 h20 h hTL hα hi hD
  | 3, hi => exact C3of3324.false_case3 h38 h39 h20 h hTL hα hi hD
  | 4, hi => exact (C4Fix3323.not_isC134Case4CorrW h h38 h39 h14 h20 hC34 hTL hα hi).elim
  | 5, hi => exact (C45.not_isC134Case5 h h38 h39 hTL hi).elim
  | n + 6, hi => exact hi.elim

end CFSG.Quasithin.H13
