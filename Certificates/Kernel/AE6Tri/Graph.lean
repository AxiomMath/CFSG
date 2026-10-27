module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.Kernel.AE6Tri.Defs
public import Certificates.Kernel.AE6Tri.Data
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Data.AE6ModelCore
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Mathieu.Gen

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6Tri

open CFSG.KS.SporSch.MOCG

meta def delta0W : Array (List Nat) :=
  #[[0], [], [4, 2, 0, 2, 6, 2, 4, 2, 0, 2, 6], [4, 2, 0, 2, 3, 4, 6, 2, 0, 2, 6],
    [2, 0, 4, 6, 2, 0, 4, 6, 2, 0, 4, 6, 2, 6], [0, 2, 0, 4, 2, 5, 6, 2, 0, 2, 4, 6, 2],
    [2, 0, 4, 6, 2, 0, 4, 6, 2, 0, 4, 6, 2, 4], [0, 2, 0, 6, 2, 4, 2, 0, 2, 4, 7, 6, 2]]

meta def graphArr (i : Nat) : Array Nat :=
  let g := CFSG.EvenSmallLie.OmegaEight.genArrs[i]!
  let d := delta0W[i]!.foldr (fun c acc => comp (CFSG.EvenSmallLie.OmegaEight.genArrs[c]!) acc)
    (idA 360)
  g ++ d.map (· + 360)

@[expose] def gdDerive : List (List Int) :=
  [[-2, 4, 2], [-8, 6, 8], [-6, -2, 6, 2], [-5, 3, 5], [-7, 3, 7]]

meta def strongGD : Array (Array Nat) :=
  strongOf 720 (#[0, 2, 3, 4, 5, 6, 7].map graphArr)
    [[-2, 4, 2], [-8, 6, 8], [-6, -2, 6, 2], [-5, 3, 5], [-7, 3, 7]]

meta def baseGD : Array Nat := #[0, 2, 1, 4, 24, 8]

end CertificateChecks.KernelAE6Tri

#ks_rawchain CertificateChecks.KernelAE6Tri.GD 720 10 48 CertificateChecks.KernelAE6Tri.strongGD
  CertificateChecks.KernelAE6Tri.baseGD 7 CertificateChecks.KernelAE6Tri.gdDerive

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.AE6Tri CFSG.KD.AE6Tri CFSG.KS.Raw

theorem kGensGD : grOK GD.S RG (dg.getD 0 []) (vl.getD 0 []) = true := by quickRfl

theorem kOrdGD : Nat.beq (rcnt (GD.LR 0) * rcnt (GD.LR 1) * rcnt (GD.LR 2) * rcnt (GD.LR 3) *
    rcnt (GD.LR 4) * rcnt (GD.LR 5)) 1290240 = true := by quickRfl

theorem kGensGDNeg : (!grOK GD.S RG (dg.getD 1 []) (vl.getD 0 [])) = true := by quickRfl

end CertificateChecks.KernelAE6Tri

end
