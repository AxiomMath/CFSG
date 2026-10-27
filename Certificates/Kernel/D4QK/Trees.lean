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

@[expose] noncomputable def GQ (l : Nat) : Nat := QT.P (Nat.add (nat_lit 1) l)

@[expose] noncomputable def GK (l : Nat) : Nat := KT.P (Nat.add (nat_lit 1) l)

@[expose] noncomputable def GZ (l : Nat) : Nat := ZT.P (Nat.add (nat_lit 1) l)

@[expose] noncomputable def GS (l : Nat) : Nat := ST.P (Nat.add (nat_lit 1) l)

theorem qHead : gtHeadK QT.P QT.PAR QT.LAB QT.N 1024 2 = true := by quickRfl

#kc_each CertificateChecks.KernelD4Q.ch300206q s
  (fun i => gtSegK GQ 14 2049 QT.N QT.P QT.PAR QT.LAB QT.W QT.S 1024 i) 0 2

#kc_forall_chunks qSegs (fun i => gtSegK GQ 14 2049 QT.N QT.P QT.PAR QT.LAB QT.W QT.S 1024 i = true)
  2 CertificateChecks.KernelD4Q.ch300206q.s 1

theorem kHead : gtHeadK KT.P KT.PAR KT.LAB KT.N 42 1 = true := by quickRfl

theorem kSeg : gtSegK GK 3 43 KT.N KT.P KT.PAR KT.LAB KT.W KT.S 42 0 = true := by quickRfl

theorem zHead : gtHeadK ZT.P ZT.PAR ZT.LAB ZT.N 7 1 = true := by quickRfl

theorem zSeg : gtSegK GZ 1 8 ZT.N ZT.P ZT.PAR ZT.LAB ZT.W ZT.S 7 0 = true := by quickRfl

theorem sHead : gtHeadK ST.P ST.PAR ST.LAB ST.N 1024 2 = true := by quickRfl

#kc_each CertificateChecks.KernelD4Q.ch300207s s
  (fun i => gtSegK GS 14 2049 ST.N ST.P ST.PAR ST.LAB ST.W ST.S 1024 i) 0 2

#kc_forall_chunks sSegs (fun i => gtSegK GS 14 2049 ST.N ST.P ST.PAR ST.LAB ST.W ST.S 1024 i = true)
  2 CertificateChecks.KernelD4Q.ch300207s.s 1

end CertificateChecks.KernelD4Q

end
