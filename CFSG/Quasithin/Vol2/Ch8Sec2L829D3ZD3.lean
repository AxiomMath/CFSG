module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LM1
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TSixB3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H

theorem not_isPSL_two_two_one_d3z {X : Type} [Group X] : ¬ IsPSL 2 2 1 X := by
  intro h
  have hadm : StatedLieAdmissible .PSL 2 2 1 :=
    (show StatedClassicalModel X .PSL 2 2 1 from h).1
  simp only [StatedLieAdmissible] at hadm
  norm_num at hadm

theorem stmtD3L3M22_holds (hE214 : ASInputs.AS_E_2_14)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (hLU : HLU82) (h825 : Stmt8_2_5) (h827 : Step827)
    (hMB0 : MB0_828) (hMB1 : MB1_828) (hMB2 : MB2_828) (hMB3 : MB3_828) (hMB4 : MB4_828)
    (hSyl : Sylow822VB_828) : StmtD3L3M22 := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hrow'
  have hS := step828Three_of hE214 h37 h38 h39 hmod h711n hcard hLU h825 h827 hMB0 hMB1 hMB2 hMB3
      hSyl
      (step828SixB_holds hE214 h37 h38 h39 hmod h711n hcard hLU h825 h827 hMB0 hMB2 hMB3 hMB4 hSyl) G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hC825 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hk1 : k = 1 := by
    have hw : ((k : ℕ) : ℕ∞) = 1 := by
      rcases hrow' with hL | hM
      · exact hC825.1.symm.trans (hC825.2.2.2.1 ⟨1, hL⟩).1
      · exact hC825.1.symm.trans (hC825.2.2.2.2.1 hM).1
    exact_mod_cast hw
  rcases hS.1 with ⟨-, ⟨eD⟩⟩ | hP | ⟨-, -, ⟨eD⟩⟩
  · exact ⟨3, Or.inl rfl, ⟨eD⟩⟩
  · exfalso
    rw [hk1] at hP
    exact not_isPSL_two_two_one_d3z hP
  · exact ⟨5, Or.inr rfl, ⟨eD⟩⟩

end CFSG.Quasithin.H13
