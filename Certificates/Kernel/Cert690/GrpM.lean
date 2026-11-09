module

public import Certificates.Data.Kernel.Cert690.Base
public import Certificates.Kernel.Cert690.GrpMData
public import Certificates.Kernel.Cert690.GrpChunk

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelC690.GrpM

open CFSG.KC.C690

theorem lenO : O.length = 51840 := by decide +kernel

theorem lenOm : Om.length = 25920 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ixO : ixOK S O = true := by decide +kernel

set_option maxHeartbeats 0 in
theorem ixOm : ixOK Sm Om = true := by decide +kernel

theorem ckOhd : O.head? = some oneF := by decide +kernel

theorem ckOphd : par.head? = some (0, 0) := by decide +kernel

theorem ckOplen : par.length = O.length := by decide +kernel

set_option maxHeartbeats 0 in
theorem ckObfs0 : bfsSeg (fun y => (idxT S).find y O.length)
    [35721076609, 35720809665, 35704292801, 35704030401, 17717821506]
    (takeR 25920 (dropR 0 O)) (fun _ c _ _ => Nat.beq c 40794) 0 1 (dropR 1 O)
    (dropR 1 par) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ckObfs1 : bfsSeg (fun y => (idxT S).find y O.length)
    [35721076609, 35720809665, 35704292801, 35704030401, 17717821506]
    (takeR 25920 (dropR 25920 O)) (fun _ c _ _ => Nat.beq c 51840) 25920 40794 (dropR 40794 O)
    (dropR 40794 par) = true := by
  decide +kernel

theorem bfsO : bfsOK (fun y => (idxT S).find y O.length)
    [35721076609, 35720809665, 35704292801, 35704030401, 17717821506] O par = true :=
  bfsOK_of_seg ckOhd ckOphd ckOplen
    (bfsSeg_chunkR (a := 0) (k := 25920) (by rw [lenO]; decide) ckObfs0
    (bfsSeg_chunkR (a := 25920) (k := 25920) (by rw [lenO]; decide) ckObfs1
    (bfsSeg_base (L := O) (a := 51840) (c := 51840) (by rw [lenO]; decide) (by rw [lenO]; rfl)
      (O.drop 51840) (par.drop 51840))))

set_option maxHeartbeats 0 in
theorem bfsOm : bfsOK (fun y => (idxT Sm).find y Om.length)
    [35721076609, 35720809665, 35704292801, 35704030401, 17718853698] Om omPar = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem invO : invK (idxT S) O.length O invC inv = true := by decide +kernel

end CertificateChecks.KernelC690.GrpM

end
