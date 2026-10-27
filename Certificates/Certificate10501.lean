module

public import Certificates.Data.Kernel.J3Dc.Defs
public import CFSG.Sporadic.Schreier.PairJ3CertInputs
import Certificates.Kernel.J3Dc.Final
import Certificates.Kernel.Census.J3.Text
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG.KD.J3Dc in
theorem certificate10501 :
    CFSG.KC.SLDc.dcCheck C CFSG.KD.J3Dc.D = true ∧
    (∀ l < 2, (CFSG.Sporadic.Schreier.j3StrongArrs[l]!).size = 6156 ∧
      ∀ p < 6156, (CFSG.Sporadic.Schreier.j3StrongArrs[l]!).getD p 0 = L l p ∧ L l p < 6156) ∧
    sgwOK = true ∧ (∀ i < 3, sgOK i = true) ∧ invOK = true ∧
    CFSG.KD.J3Dc.D.sep = [0, 1, 3, 2] ∧ CFSG.KD.J3Dc.D.mw.length = 5 ∧ (List.range 5).all memOK = true ∧
    (List.range 5).map (fun j => (Om j).lbl.size) = [1, 3, 3, 9, 15] ∧
    sbOK = true ∧ Sb.lbl.size = 128 := CFSG.KD.J3Dc.facts

end Certificates
