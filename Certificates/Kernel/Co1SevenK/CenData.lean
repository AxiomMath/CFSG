module

public import Certificates.Kernel.Co1SevenK.Dag
public meta import Certificates.Kernel.SporSch.Co1.GenBfs
public meta import Certificates.Kernel.Co1SevenK.Dag
public meta import Certificates.Kernel.Sporadic.OrbRecGen
public meta import Std.Data.HashMap
public import Certificates.Kernel.SporSch.Co1.GenBfs
public import Certificates.Kernel.Sporadic.OrbRecGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.Sporadic.Co1Schreier.Native Timmesfeld.Co1Seven

meta def cenGA : Array Rows := (instA.gens.map (rowAt dagD.1)).toArray

meta def cenGB : Array Rows := (instB.gens.map (rowAt dagD.1)).toArray

meta def closD (G : Array Rows) : Array Nat × Array Nat × Array Nat := Id.run do
  let pts := (CFSG.Sporadic.Co1.TwoBNative.gtBFS G 100000).pts
  let good := isTarget qsList
  let F := fusData pts G.toList good
  let N := pts.size
  let mut pos : Std.HashMap Rows Nat := ∅
  for k in [0:N] do
    pos := pos.insert pts[k]! k
  let M := min N 64
  let invs := (Array.range M).map fun a => inv pts[a]!
  let mut wit : Array Nat := Array.replicate N 0
  for r in [0:N] do
    if good pts[r]! && (F[r]!).1 == r then
      let x := pts[r]!
      let mut found := false
      for a in [0:M] do
        if found then break
        let ca := conjCand pts[a]! invs[a]! x
        for b in [0:M] do
          if found then break
          let y := mul (mul x ca) (conjCand pts[b]! invs[b]! x)
          if y != one () && pow y 7 == one () then
            let ai := pos.getD invs[a]! N
            let bi := pos.getD invs[b]! N
            wit := wit.set! r (a + 65536 * (ai + 65536 * (b + 65536 * bi)))
            found := true
  return (F.map (·.1), F.map (·.2), wit)

meta def closA : Array Nat × Array Nat × Array Nat := closD cenGA

meta def closB : Array Nat × Array Nat × Array Nat := closD cenGB

meta def closAR : Array Nat := closA.1
meta def closAC : Array Nat := closA.2.1
meta def closAW : Array Nat := closA.2.2
meta def closBR : Array Nat := closB.1
meta def closBC : Array Nat := closB.2.1
meta def closBW : Array Nat := closB.2.2

end CertificateChecks.KernelCo1SevenK

#kss_co1gt CertificateChecks.KernelCo1SevenK.CA CertificateChecks.KernelCo1SevenK.cenGA 100000

#kss_co1gt CertificateChecks.KernelCo1SevenK.CB CertificateChecks.KernelCo1SevenK.cenGB 100000

#kc_nattree CertificateChecks.KernelCo1SevenK.FA.R CertificateChecks.KernelCo1SevenK.closAR
#kc_nattree CertificateChecks.KernelCo1SevenK.FA.C CertificateChecks.KernelCo1SevenK.closAC
#kc_nattree CertificateChecks.KernelCo1SevenK.FA.W CertificateChecks.KernelCo1SevenK.closAW
#kc_nattree CertificateChecks.KernelCo1SevenK.FB.R CertificateChecks.KernelCo1SevenK.closBR
#kc_nattree CertificateChecks.KernelCo1SevenK.FB.C CertificateChecks.KernelCo1SevenK.closBC
#kc_nattree CertificateChecks.KernelCo1SevenK.FB.W CertificateChecks.KernelCo1SevenK.closBW

end
