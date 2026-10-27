module

public import Certificates.Kernel.AE6Q8.Chain
public import Certificates.Kernel.AE6Core.Checks
public import Certificates.Data.Kernel.AE6FWN
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6FW

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.KGC31P CFSG.KC.AE6F CFSG.KC.AE6Core
  CFSG.KC.AE6FW Certificates.AE6Model
open CertificateChecks.KernelAE6F (RG WL)
open CertificateChecks.KernelAE6Q8

@[expose] noncomputable def SL : List Nat :=
  pfilterProducts 360 9 (fun _ => true) (trPL 360 9 SC.LR SC.TR 5) (pidn 360 9) []

@[expose] noncomputable def TPN : List (Nat × Nat) :=
  twinPairsN RG (cwN CertificateChecks.KernelAE6Core.CW.chars)

@[expose] noncomputable def KA : List Nat :=
  frameCandsN TPN 0 ++ (frameCandsN TPN 1 ++ (frameCandsN TPN 2 ++ frameCandsN TPN 3))

@[expose] noncomputable def SIG : List Nat := SL.map fun T => bitsOf (KA.map (commF T))

@[expose] noncomputable def WB : Nat := bitsOf (KA.map fun X => WL.all fun T => commF T X)

theorem kTRS : (trPL 360 9 SC.LR SC.TR 5).all (fun L => L.all fun t =>
    permOK 360 9 (mask 9) (360 * 9) t (pinv 360 9 t)) = true := by decide +kernel

theorem kComm : fwCommN WL = true := by decide +kernel

theorem kInSFrames : (fwInSN SL WL && fwFramesI SIG WB (frameCandsN TPN 0).length
    (frameCandsN TPN 1).length (frameCandsN TPN 2).length (frameCandsN TPN 3).length) = true := by
  decide +kernel

theorem kNorm : fwNormN TPN WL = true := by decide +kernel

theorem kMeet : fwMeetN TPN WL = true := by decide +kernel

end CertificateChecks.KernelAE6FW

end
