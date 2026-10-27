module

public import Certificates.Kernel.Co1M.Regs10071
public import Certificates.Data.Kernel.Co1Odd71
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KD.Co1Odd CFSG.KLie.CT

theorem z71_gens : (Z1G == [getL 0 cmRP71 81, getL 0 cmRP71 82] &&
    Z2G == [getL 0 cmRP71 83, getL 0 cmRP71 84]) = true := by quickRfl

theorem z71_head1 : (Z1P.length == 1344 && Z1Par.length == 1344 && Z1Lab.length == 1344 &&
    Z1P.getD 0 0 == idF 24) = true := by quickRfl

theorem z71_dist1 : distinctL Z1P = true := by quickRfl

theorem z71_tree2 : (treeOK71 Z2G Z2P Z2Par Z2Lab 96 && distinctL Z2P && canonL Z2P) = true := by
  quickRfl

theorem z71_neg : (!treeOK71 Z2G Z2P (Z2Par.set 7 0) Z2Lab 96 && !distinctL (Z2P.getD 5 0 :: Z2P) &&
    !noConjOK Z2P []) = true := by quickRfl

end CertificateChecks.KernelCo1M

end
