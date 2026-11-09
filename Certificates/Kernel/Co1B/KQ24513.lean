module

public import Certificates.Kernel.Co1B.Dag24513
public import Certificates.Kernel.Co1B.Bfs24513
public import Certificates.Data.Kernel.SporSch.Co1BfsSeg
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSegSound
public import CFSG.Certificates.Kernel.Common.EachTrue
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Syl2B

open CFSG.KS.SporSch.M24 CFSG.EvenSporadicStandard.TwoCo1.HypOne

@[expose] noncomputable def SM (l : Nat) : Nat := S2.M (sylIdxB.getD l 0)

theorem bfsK_of_gtPinK {GM : Nat → Nat} {ng cap N : Nat} {P PAR LAB W S : Nat → Nat}
    (h : gtPinK GM ng cap N P PAR LAB W S = true) :
    bfsK (gtStepK GM) P PAR LAB W S ng cap N idM = true := by
  unfold gtPinK at h
  simp only [MatL.bAnd_eq, Bool.and_eq_true] at h
  exact h.1

theorem kQh : gtHeadK ST.P ST.PAR ST.LAB ST.N 256 128 = true := by quickRfl

#kc_each CertificateChecks.KernelCo1B.Syl2B.tq24513 s
  (fun i => gtSegK SM 4 32769 ST.N ST.P ST.PAR ST.LAB ST.W ST.S 256 i) 0 128

#kc_forall_chunks kQs (fun i => gtSegK SM 4 32769 ST.N ST.P ST.PAR ST.LAB ST.W ST.S 256 i = true)
  128 CertificateChecks.KernelCo1B.Syl2B.tq24513.s 1

theorem kQ : bfsK (gtStepK SM) ST.P ST.PAR ST.LAB ST.W ST.S 4 32769 ST.N idM = true :=
  bfsK_of_gtPinK (gtPinK_of_seg kQh kQs)

end CertificateChecks.KernelCo1B.Syl2B

end
