module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.Kernel.AE6E8.Defs
public import Certificates.Kernel.AE6Tri.Data
public import Certificates.Kernel.AE6E8.Chain16
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Data.AE6ModelCore
public meta import Certificates.Data.AE6CertBAE8
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6E8

open CFSG.KS.SporSch.MOCG

@[expose] def grL : List Nat := [0, 2, 3, 4, 5, 6, 7, 8]

@[expose] def grDeriveK : List (List Int) :=
  [[-2, 4, 2], [-9, 6, 9], [-6, -2, 6, 2], [-5, 3, 5], [-7, 3, 7]]

meta def grArr (j : Nat) : Array Nat :=
  if h : j < 7 then
    Array.ofFn (fun p : Fin 16 =>
        (Certificates.AE6CertB.wr16 (Certificates.AE6CertB.ae8Gen ⟨j, h⟩) p).val) ++
      (CFSG.EvenSmallLie.OmegaEight.genArrs[[0, 2, 3, 4, 5, 6, 7][j]!]!).map (· + 16)
  else
    (Array.range 16).map (fun x => x ^^^ 1) ++ (Array.range 360).map (· + 16)

meta def strongGR : Array (Array Nat) :=
  strongOf 376 ((Array.range 8).map grArr)
    [[-2, 4, 2], [-9, 6, 9], [-6, -2, 6, 2], [-5, 3, 5], [-7, 3, 7]]

meta def baseGR : Array Nat := #[16, 18, 17, 20, 40, 24, 0]

end CertificateChecks.KernelAE6E8

#ks_rawchain CertificateChecks.KernelAE6E8.GR 376 9 24 CertificateChecks.KernelAE6E8.strongGR
  CertificateChecks.KernelAE6E8.baseGR 8 CertificateChecks.KernelAE6E8.grDeriveK

namespace CertificateChecks.KernelAE6E8

open CFSG.KC.AE6E8 CFSG.KD.AE6Tri CFSG.KS.Raw

theorem kGensGR : sumOK GR.S (wSel E8.S) RG grL = true := by quickRfl

theorem kOrdGR : Nat.beq (rcnt (GR.LR 0) * rcnt (GR.LR 1) * rcnt (GR.LR 2) * rcnt (GR.LR 3) *
    rcnt (GR.LR 4) * rcnt (GR.LR 5) * rcnt (GR.LR 6)) 2580480 = true := by quickRfl

theorem kGensGRNeg : (!sumOK GR.S (wSel E8.S) RG [0, 2, 3, 4, 6, 5, 7, 8]) = true := by quickRfl

end CertificateChecks.KernelAE6E8

end
