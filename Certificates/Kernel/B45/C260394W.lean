module

public import Certificates.Kernel.SporSch.Th.GenV4
meta import Certificates.Data.SmithB45ExcRuData
import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

namespace CertificateChecks.KernelB45.C260394

open CFSG.Quasithin.B45Exc.Ru CFSG.Quasithin.B45Exc.Tab

meta partial def chains : Nat → List Nat → List (List Nat)
  | 0, l => [l]
  | k + 1, l => (ruTab.greedyExtI l).flatMap fun x => chains k (x :: l)

meta def hits (S : List Nat) (w : DblWit) : Bool := w.e.all S.contains

meta partial def cover (L : List (List Nat)) (W : List (Nat × DblWit)) (acc : List Nat) :
    List Nat :=
  if L.isEmpty then acc.reverse else
  let best := W.foldl (fun (b : Nat × Nat) (p : Nat × DblWit) =>
    let c := (L.filter fun S => hits S p.2).length
    if c > b.2 then (p.1, c) else b) (0, 0)
  if best.2 == 0 then [] else
  match W.find? fun p => p.1 == best.1 with
  | some (_, w) => cover (L.filter fun S => !hits S w) W (best.1 :: acc)
  | none => []

meta def wi : List Nat :=
  cover ((chains 5 []).map ruTab.subprodsI) (ruDblWits.zipIdx.map fun p => (p.2, p.1)) []

meta def wq : List Nat := wi.map fun i =>
  ((ruDblWits[i]?.map (·.e)).getD []).zipIdx.foldl (fun acc p => acc ||| (p.1 <<< (9 * p.2))) 0

meta def wn : List Nat := [wi.length]

end CertificateChecks.KernelB45.C260394

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelB45.C260394.WI include_bytes "data/C260394W.WI.items" 601 1154492774010569221
#kc_items CertificateChecks.KernelB45.C260394.WQ include_bytes "data/C260394W.WQ.items" 1052 7190043477041195004
#kc_items CertificateChecks.KernelB45.C260394.WN include_bytes "data/C260394W.WN.items" 5 16632121959440216109
