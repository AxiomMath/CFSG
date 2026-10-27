module

public import Certificates.Data.Kernel.F2TriSep
public import Certificates.Kernel.Co2W11.SepData
public import Certificates.Kernel.LocalComp.Co2Ops
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo2W11

open CFSG.KC.F2TriSep CFSG.KC.M1F2 CertificateChecks.KernelLC.Co2Ops

@[expose] noncomputable def gensOf (ws : List (List Bool)) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun w _ ih => wordB 22 SA.M SB.M w (idF 22) :: ih) ws

theorem sep0_ok : triK 22 (gensOf S0.words) S0.tree S0.masks S0.ts S0.F S0.Dm S0.w = true := by
  quickRfl

theorem sep1_ok : triK 22 (gensOf S1.words) S1.tree S1.masks S1.ts S1.F S1.Dm S1.w = true := by
  quickRfl

theorem sep2_ok : triK 22 (gensOf S2.words) S2.tree S2.masks S2.ts S2.F S2.Dm S2.w = true := by
  quickRfl

theorem fix0_ok : fixL 22 (gensOf S0.words) S0.w = true := by quickRfl

theorem fix1_ok : fixL 22 (gensOf S1.words) S1.w = true := by quickRfl

theorem fix2_ok : fixL 22 (gensOf S2.words) S2.w = true := by quickRfl

theorem spin0_ok :
    spinK 22 (gensOf S0.words) S0.spinTree S0.spinV S0.spinE S0.spinRi = true := by
  quickRfl

end CertificateChecks.KernelCo2W11

end
