module

public import Certificates.Kernel.D4QK.Data
public import Certificates.Data.Kernel.SporSch.Co1BfsSeg
public import CFSG.Certificates.Kernel.Common.EachTrue
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelD4Q

open CFSG.KS.SporSch.M24 (gtHeadK gtSegK)

@[expose] noncomputable def GB (l : Nat) : Nat := BT.P (Nat.add (nat_lit 1) l)

theorem bHead : gtHeadK BT.P BT.PAR BT.LAB BT.N 1024 28 = true := by quickRfl

#kc_each CertificateChecks.KernelD4Q.ch300207b s
  (fun i => gtSegK GB 4 28673 BT.N BT.P BT.PAR BT.LAB BT.W BT.S 1024 i) 0 28

#kc_forall_chunks bSegs (fun i => gtSegK GB 4 28673 BT.N BT.P BT.PAR BT.LAB BT.W BT.S 1024 i = true)
  28 CertificateChecks.KernelD4Q.ch300207b.s 1

end CertificateChecks.KernelD4Q

end
