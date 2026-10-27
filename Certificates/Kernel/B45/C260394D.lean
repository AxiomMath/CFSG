module

public import Certificates.Kernel.SporSch.Th.GenV4
meta import Certificates.Data.SmithB45ExcRuData
import CFSG.Assembly.LowTwoRankDefs

namespace CertificateChecks.KernelB45.C260394

open CFSG.Quasithin.B45Exc.Ru CFSG.Quasithin.B45Exc.Tab CFSG.Sporadic.RuSchreier

meta def code (x : Array Nat) : Nat :=
  let L0 := ruLevS[0]!
  let L1 := ruLevS[1]!
  let a := L0.pos[x[1]!]!
  let b := L1.pos[(L0.trInv[a]!)[x[0]!]!]!
  8 * a + b

meta def cd : List Nat := ru2AInv.toList.map code

meta def ix : List Nat :=
  ((cd.zipIdx).foldl (fun (A : Array Nat) (p : Nat × Nat) => A.set! p.1 p.2)
    (Array.replicate 16384 495)).toList

meta def k1 : List Nat := ru2AInv.toList.map (fun x => x[1]!) ++ [1]

meta def k0 : List Nat := ru2AInv.toList.map (fun x => x[0]!) ++ [0]

meta def cm : List Nat := (List.range ruTab.m).map fun i =>
  (List.range ruTab.m).foldl (fun acc j => if ruTab.commAt i j then acc ||| (1 <<< j) else acc) 0

meta def pr : List Nat := (List.range ruTab.m).map fun i =>
  (List.range ruTab.m).foldl (fun acc j =>
    if ruTab.commAt i j then acc ||| (ruTab.prodAt i j <<< (9 * j)) else acc) 0

end CertificateChecks.KernelB45.C260394

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelB45.C260394.CD CertificateChecks.KernelB45.C260394.cd
#kss_natlist CertificateChecks.KernelB45.C260394.IX CertificateChecks.KernelB45.C260394.ix
#kss_natlist CertificateChecks.KernelB45.C260394.K1 CertificateChecks.KernelB45.C260394.k1
#kss_natlist CertificateChecks.KernelB45.C260394.K0 CertificateChecks.KernelB45.C260394.k0
#kss_natlist CertificateChecks.KernelB45.C260394.CM CertificateChecks.KernelB45.C260394.cm
#kss_natlist CertificateChecks.KernelB45.C260394.PR CertificateChecks.KernelB45.C260394.pr
