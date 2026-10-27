module

public import CFSG.Sporadic.Schreier.J4SElevenData
import Certificates.Kernel.SporSch.J4S11.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native in
open CFSG.Sporadic.SmallF2.Native in
theorem certificate2170 : (max7Prog.map instrCode = [
      [0, 1, 2, 3], [0, 3, 2, 4], [0, 3, 4, 5], [0, 3, 5, 6], [0, 6, 4, 5], [2, 4, 4, 3],
      [2, 8, 5, 4], [1, 4, 5], [0, 5, 3, 6], [0, 6, 4, 3], [0, 1, 3, 4], [0, 4, 3, 5], [2, 3, 5, 6],
      [0, 4, 4, 5], [0, 6, 5, 3], [2, 6, 4, 5], [0, 5, 3, 4], [2, 20, 4, 3], [0, 3, 2, 5],
      [0, 2, 3, 6], [1, 6, 3], [0, 3, 5, 6], [2, 3, 6, 2], [0, 4, 2, 3], [0, 4, 3, 5], [2, 7, 5, 3],
      [1, 4, 5], [0, 5, 2, 6], [0, 2, 6, 5], [2, 8, 4, 2], [0, 2, 5, 6], [1, 6, 5], [0, 1, 4, 2],
      [0, 5, 3, 4], [0, 4, 6, 1]]
    )
    ∧ (max7Prog.all (Instr.lt 7) = true)
    ∧ (O.eq (O.mul QZn.1 QXn.1) (O.mul QXn.1 QZn.1) = true ∧
      O.eq (O.mul QZn.1 QYn.1) (O.mul QYn.1 QZn.1) = true ∧ O.vne (O.vmul (O.unit 0) QZn.1)
        (O.unit 0) = true
    )
    ∧ (expOK QXn.1 QYn.1 QZn.1 = true)
    ∧ (centerOK QXn.1 QYn.1 = true)
    ∧ (O.normalFormOK 11 [QXn.1, QYn.1, QZn.1] 0 = true)
    ∧ (O.conjOK H1n.1 QXn.1 (CFSG.Sporadic.J4Schreier.qWord 7 3 2).1 = true ∧
      O.conjOK H1n.1 QYn.1 (CFSG.Sporadic.J4Schreier.qWord 3 3 9).1 = true ∧ O.conjOK H1n.1 QZn.1 QZn.1 = true ∧
      O.conjOK H2n.1 QXn.1 (CFSG.Sporadic.J4Schreier.qWord 8 6 3).1 = true ∧ O.conjOK H2n.1 QYn.1 (CFSG.Sporadic.J4Schreier.qWord 10 5 8).1 = true ∧
      O.conjOK H2n.1 QZn.1 (O.pow QZn.1 2) = true
    )
    ∧ (fixDimOK QXn.1 fixP_qx fixPinv_qx fixR_qx 12 = true ∧
      fixDimOK QYn.1 fixP_qy fixPinv_qy fixR_qy 12 = true ∧
      fixDimOK QZn.1 fixP_qz fixPinv_qz fixR_qz 2 = true
    )
    ∧ (fixDimOK C23n.1 fixP_c23 fixPinv_c23 fixR_c23 2 = true)
    ∧ (O.eq (O.pow U8n.1 8) O.one = true ∧ O.eq (O.mul W2n.1 W2n.1) O.one = true ∧
      O.conjOK W2n.1 U8n.1 (O.pow U8n.1 3) = true ∧ sixteenOK U8n.1 W2n.1 = true
    )
    ∧ (∀ v : Fin 2 → ZMod 11, v ≠ 0 →
      evalW (fwdW v) ![1, 0] = v ∧ evalW (bwdW v) v = ![1, 0]
    ) := KernelSporSch.J4E7.facts

end Certificates
