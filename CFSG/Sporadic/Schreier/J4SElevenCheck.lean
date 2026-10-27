module

public import CFSG.Sporadic.Schreier.J4SElevenData
public meta import CFSG.Sporadic.Schreier.J4SElevenData
public import Certificates.Certificate2170
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs
public import CFSG.Sporadic.Th.F2Spec
public meta import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.GLQ CFSG.SectionRank.Native CFSG.Sporadic.SmallF2.Native

theorem max7Prog_code : max7Prog.map instrCode = [
    [0, 1, 2, 3], [0, 3, 2, 4], [0, 3, 4, 5], [0, 3, 5, 6], [0, 6, 4, 5], [2, 4, 4, 3],
    [2, 8, 5, 4], [1, 4, 5], [0, 5, 3, 6], [0, 6, 4, 3], [0, 1, 3, 4], [0, 4, 3, 5], [2, 3, 5, 6],
    [0, 4, 4, 5], [0, 6, 5, 3], [2, 6, 4, 5], [0, 5, 3, 4], [2, 20, 4, 3], [0, 3, 2, 5],
    [0, 2, 3, 6], [1, 6, 3], [0, 3, 5, 6], [2, 3, 6, 2], [0, 4, 2, 3], [0, 4, 3, 5], [2, 7, 5, 3],
    [1, 4, 5], [0, 5, 2, 6], [0, 2, 6, 5], [2, 8, 4, 2], [0, 2, 5, 6], [1, 6, 5], [0, 1, 4, 2],
    [0, 5, 3, 4], [0, 4, 6, 1]] :=
  Certificates.certificate2170.1

theorem max7Prog_lt : max7Prog.all (Instr.lt 7) = true :=
  Certificates.certificate2170.2.1

theorem q11_basic : O.eq (O.mul QZn.1 QXn.1) (O.mul QXn.1 QZn.1) = true ∧
    O.eq (O.mul QZn.1 QYn.1) (O.mul QYn.1 QZn.1) = true ∧ O.vne (O.vmul (O.unit 0) QZn.1)
      (O.unit 0) = true :=
  Certificates.certificate2170.2.2.1

theorem q11_exp : expOK QXn.1 QYn.1 QZn.1 = true :=
  Certificates.certificate2170.2.2.2.1

theorem q11_center : centerOK QXn.1 QYn.1 = true :=
  Certificates.certificate2170.2.2.2.2.1

theorem q11_normalForm : O.normalFormOK 11 [QXn.1, QYn.1, QZn.1] 0 = true :=
  Certificates.certificate2170.2.2.2.2.2.1

theorem q11_conj : O.conjOK H1n.1 QXn.1 (qWord 7 3 2).1 = true ∧
    O.conjOK H1n.1 QYn.1 (qWord 3 3 9).1 = true ∧ O.conjOK H1n.1 QZn.1 QZn.1 = true ∧
    O.conjOK H2n.1 QXn.1 (qWord 8 6 3).1 = true ∧ O.conjOK H2n.1 QYn.1 (qWord 10 5 8).1 = true ∧
    O.conjOK H2n.1 QZn.1 (O.pow QZn.1 2) = true :=
  Certificates.certificate2170.2.2.2.2.2.2.1

theorem q11_fix : fixDimOK QXn.1 fixP_qx fixPinv_qx fixR_qx 12 = true ∧
    fixDimOK QYn.1 fixP_qy fixPinv_qy fixR_qy 12 = true ∧
    fixDimOK QZn.1 fixP_qz fixPinv_qz fixR_qz 2 = true :=
  Certificates.certificate2170.2.2.2.2.2.2.2.1

theorem c23_fix : fixDimOK C23n.1 fixP_c23 fixPinv_c23 fixR_c23 2 = true :=
  Certificates.certificate2170.2.2.2.2.2.2.2.2.1

theorem sixteen_check : O.eq (O.pow U8n.1 8) O.one = true ∧ O.eq (O.mul W2n.1 W2n.1) O.one = true ∧
    O.conjOK W2n.1 U8n.1 (O.pow U8n.1 3) = true ∧ sixteenOK U8n.1 W2n.1 = true :=
  Certificates.certificate2170.2.2.2.2.2.2.2.2.2.1

theorem trans_check : ∀ v : Fin 2 → ZMod 11, v ≠ 0 →
    evalW (fwdW v) ![1, 0] = v ∧ evalW (bwdW v) v = ![1, 0] :=
  Certificates.certificate2170.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.J4Schreier
