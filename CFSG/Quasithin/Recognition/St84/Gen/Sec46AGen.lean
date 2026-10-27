module

public import CFSG.Quasithin.Recognition.St84.Sec46Cases
public import CFSG.Quasithin.Recognition.St84.Gen.Sec46D4qDefs

import CFSG.Quasithin.Recognition.St84.Sec46A4
import CFSG.Quasithin.Recognition.St84.Gen.Sec46A5h

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

theorem CaseA.toGen {X : Setup Γ G} (A : X.CaseA) : X.CaseAGen := by
  have hn0 : 1 ≤ X.n 0 := by have h := A.hyp.two_le_n 0; omega
  have h3 := X.caseA_3 A
  have h5d := X.caseA_5d A
  have h5f := X.caseA_5f A
  have h5g := X.caseA_5g A
  have hW := X.caseA_w1Hyp A
  have hindec : ⁅X.Q 0, oTwoRes (X.L 0)⁆ = X.Q 0 :=
    X.caseA_indec_Q0 hn0 h5d.1 (X.caseA_comm_D_Ki_zero A) h5f.1 h5d.2.2.2.2.2
  have hZ01 : X.Z 0 ≤ X.Z 1 := by rw [h3.2.2.2.2.2.2.1]; exact le_sup_left
  exact
    { two_le_n1 := A.hyp.two_le_n 1
      n1_le_n0 := hW.n1_le_n0
      card_S := (X.caseA_card A).1
      card_Q0 := by simpa using (X.caseA_card A).2 0
      card_Q1 := by
        have hn2 : X.n 2 = X.n 0 := by simpa using X.n_add 1 0
        have h := (X.caseA_card A).2 1
        rw [show (1 : ℤ) + 1 = 2 by norm_num, hn2] at h
        rw [h]
        congr 1
        ring
      Z0_eq := h3.2.1
      card_Z0 := h3.2.2.2.1
      natZ1 := h3.2.2.2.2.2.1
      center_Q0 := h5g.1
      special_Q0 := h5g.2.1
      sec_Q0 := h5g.2.2
      indec_Q0 := hindec
      perfect_L0 := X.caseA_perfect_L0 (A.hyp.two_le_n 0) hindec
      normal_A1 := (X.caseA_5b A).1
      sec_W1 := hW.sec
      irred_W1 := hW.irred
      fpf_W1 := hW.fpf
      A1_eq := h5d.1
      D_inf := h5d.2.1
      card_D := h5d.2.2.1
      elem_A1 := h5d.2.2.2.1
      comm_A1 := h5d.2.2.2.2.1
      comm_D := h5f.1
      D_cent := h5f.2
      gen_Q0 := X.caseA_gen_Q0 hn0 h5g.2.2 hZ01 h5d.1 h5d.2.2.1
        h5d.2.2.2.2.2 hindec }

end Setup

end CFSG.Quasithin.St84

end
