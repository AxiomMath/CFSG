module

public import Certificates.Data.Kernel.D43.TreePt
public import Certificates.Kernel.D43.TreeData
public import Certificates.Kernel.D43.HexG
public import CFSG.Certificates.Kernel.Common.EachStep
public import CFSG.Certificates.Kernel.Common.ForallChunks

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelD43

open CFSG.KC.D43 CFSG.KC.Enum

@[expose] noncomputable def pt3c (c : Nat) : Bool := ptChunk GX.F TW c

end CertificateChecks.KernelD43

#kc_each_step CertificateChecks.KernelD43.pt3c 0 104 1 as CertificateChecks.KernelD43.d43pt3_

namespace CertificateChecks.KernelD43

#kc_forall_chunks pt3 (fun c => pt3c c = true) 104 CertificateChecks.KernelD43.d43pt3_ 1

open CFSG.KC.D43

theorem line3 : lineAll GX.F TW = true := by decide +kernel

theorem aptImg3 : (Nat.beq (lAp GX.F TW 0 0) 0 && Nat.beq (lAp GX.F TW 0 6) 186 &&
    Nat.beq (lAp GX.F TW 0 479) 15916 && Nat.beq (lAp GX.F TW 0 26571) 26571 &&
    Nat.beq (lAp GX.F TW 0 15916) 479 && Nat.beq (lAp GX.F TW 0 186) 6 &&
    Nat.beq (lAp GX.F TW 1 0) 6 && Nat.beq (lAp GX.F TW 1 6) 0 &&
    Nat.beq (lAp GX.F TW 1 479) 186 && Nat.beq (lAp GX.F TW 1 26571) 15916 &&
    Nat.beq (lAp GX.F TW 1 15916) 26571 && Nat.beq (lAp GX.F TW 1 186) 479) = true := by
  decide +kernel

theorem negPt3 : (!(lineChk GX.F TW 0 1 && lineChk GX.F TW 0 2 && lineChk GX.F TW 0 6) &&
    !movesB GX.F TW 2 0 && !movesB GX.F TW 3 0) = true := by
  decide +kernel

end CertificateChecks.KernelD43

end
