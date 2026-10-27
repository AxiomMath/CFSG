module

public import Certificates.Kernel.SporSch.HeT.CntData
public import Certificates.Data.Kernel.SporSch.HeCube
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeInputs
public meta import Certificates.Kernel.SporSch.HeT.CntData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Chain.He12636

open CertificateChecks.KernelSporSch.HeCn CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He
open CFSG.Monster.B.Co2.Native

meta def ys : Array (Array Nat) := #[heThreeBA, heThreeBB]

meta def cbCnt (lo len : Nat) : Nat := Id.run do
  let L2 := lv[2]!
  let L3 := lv[3]!
  let L4 := lv[4]!
  let mut s := 0
  for k1 in [lo:lo + len] do
    for k2 in [0:L2.pts.size] do
      for k3 in [0:L3.pts.size] do
        for k4 in [0:L4.pts.size] do
          let nf := #[0, k1, k2, k3, k4]
          if [0, 1, 2, 3, 4].all (fun b => ev nf (ev nf (ev nf b)) == b) then
            s := s + 1
  return s

meta def permsM : Array (Array Nat) :=
  let xs := ys.map xOf
  #[xs[0]!, invCand 8330 xs[0]!, xs[1]!, invCand 8330 xs[1]!]

meta def natsM : List Nat :=
  (List.range 2).map (fun i => packNF (cOf ys[i]!)) ++
    (List.range 35).map (fun q => cbCnt (q * 128) 128)

meta def vOf (i : Nat) : Array Nat :=
  let x := xOf ys[i]!
  let y := ys[i]!
  (Array.range 8330).map fun k0 => srchCnt x y k0 1
meta def vaM : Array Nat := vOf 0
meta def vbM : Array Nat := vOf 1

meta def xaM : Array Nat := xOf ys[0]!
meta def xbM : Array Nat := xOf ys[1]!
meta def yaM : Array Nat := ys[0]!
meta def ybM : Array Nat := ys[1]!

meta def rzA : Array Nat × Array Nat := CertificateChecks.KernelSporSch.HeCn.orbRZ xaM yaM
meta def rzB : Array Nat × Array Nat := CertificateChecks.KernelSporSch.HeCn.orbRZ xbM ybM
meta def raM : Array Nat := rzA.1
meta def zaM : Array Nat := rzA.2
meta def rbM : Array Nat := rzB.1
meta def zbM : Array Nat := rzB.2

end CertificateChecks.KernelCo2Chain.He12636

#kss_perms CertificateChecks.KernelCo2Chain.H36P 14 CertificateChecks.KernelCo2Chain.He12636.permsM

#krowsw CertificateChecks.KernelCo2Chain.H36RXA 14 CertificateChecks.KernelCo2Chain.He12636.xaM
#krowsw CertificateChecks.KernelCo2Chain.H36RXB 14 CertificateChecks.KernelCo2Chain.He12636.xbM
#krowsw CertificateChecks.KernelCo2Chain.H36RYA 14 CertificateChecks.KernelCo2Chain.He12636.yaM
#krowsw CertificateChecks.KernelCo2Chain.H36RYB 14 CertificateChecks.KernelCo2Chain.He12636.ybM
#krowsw CertificateChecks.KernelCo2Chain.H36VA 12 CertificateChecks.KernelCo2Chain.He12636.vaM
#krowsw CertificateChecks.KernelCo2Chain.H36VB 12 CertificateChecks.KernelCo2Chain.He12636.vbM
#krowsw CertificateChecks.KernelCo2Chain.H36RA 14 CertificateChecks.KernelCo2Chain.He12636.raM
#krowsw CertificateChecks.KernelCo2Chain.H36ZA 80 CertificateChecks.KernelCo2Chain.He12636.zaM
#krowsw CertificateChecks.KernelCo2Chain.H36RB 14 CertificateChecks.KernelCo2Chain.He12636.rbM
#krowsw CertificateChecks.KernelCo2Chain.H36ZB 80 CertificateChecks.KernelCo2Chain.He12636.zbM

#knatlist CertificateChecks.KernelCo2Chain.He12636.nats CertificateChecks.KernelCo2Chain.He12636.natsM

namespace CertificateChecks.KernelCo2Chain.He12636

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.HeCn CertificateChecks.KernelCo2Chain CertificateChecks.KernelSpor

@[expose] noncomputable def XA : Nat := H36P 0
@[expose] noncomputable def XAI : Nat := H36P 1
@[expose] noncomputable def XB : Nat := H36P 2
@[expose] noncomputable def XBI : Nat := H36P 3

@[expose] noncomputable def FA : Nat := nats.getD 0 0
@[expose] noncomputable def FB : Nat := nats.getD 1 0

@[expose] noncomputable def VA (k : Nat) : Nat := CFSG.KS.Row.rg 12 (mask 12) H36VA 0 k
@[expose] noncomputable def VB (k : Nat) : Nat := CFSG.KS.Row.rg 12 (mask 12) H36VB 0 k

@[expose] noncomputable def C (q : Nat) : Nat := nats.getD (Nat.add 2 q) 0

@[expose] noncomputable def cbB (V : Nat → Nat) (q : Nat) : Bool :=
  Nat.beq (cnt0R HeC.LR (cbK 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT CFSG.Sporadic.HeldB.heBase)
    (Nat.mul q 128) 128) (V q)

@[expose] noncomputable def cjA (s : Nat) : Bool := cjB H36RXA H36RYA FA s
@[expose] noncomputable def cjB' (s : Nat) : Bool := cjB H36RXB H36RYB FB s
@[expose] noncomputable def cb (q : Nat) : Bool := cbB C q

@[expose] noncomputable def RA (k : Nat) : Nat := CFSG.KS.Row.rg 14 (mask 14) H36RA 0 k
@[expose] noncomputable def ZA (k : Nat) : Nat := CFSG.KS.Row.rg 80 (mask 80) H36ZA 0 k
@[expose] noncomputable def RB (k : Nat) : Nat := CFSG.KS.Row.rg 14 (mask 14) H36RB 0 k
@[expose] noncomputable def ZB (k : Nat) : Nat := CFSG.KS.Row.rg 80 (mask 80) H36ZB 0 k
@[expose] noncomputable def orA36 (s : Nat) : Bool := orB H36RXA H36RYA VA RA ZA 8330 s
@[expose] noncomputable def orB36 (s : Nat) : Bool := orB H36RXB H36RYB VB RB ZB 8330 s

end CertificateChecks.KernelCo2Chain.He12636

end
