module

public import Certificates.Kernel.Co1Surj.Data
public import Certificates.Kernel.VecCert.Co1.Data
public import Certificates.Data.Kernel.SurjKChain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1Surj

open CFSG.KC.SurjK CFSG.KC.SurjChain CFSG.KC.M1F2 CFSG.KC.VecK
open CFSG.KS (lget)
open CFSG.Sporadic.Bridge.SurjD.Native

@[expose] noncomputable def Li : List (List Int) := IW.W

@[expose] noncomputable def Ls : List (List Int) := SW.W

@[expose] noncomputable def Ims : List Nat :=
  Li.map (wordRF 24 (chainF CertificateChecks.KernelVec.Co1.LM))

@[expose] noncomputable def ImsI : List Nat :=
  Li.map fun w => wordRF 24 (chainF CertificateChecks.KernelVec.Co1.LM) (invWord w)

theorem kIT : wordsK IT.chars IW.W = true := by quickRfl
theorem kST : wordsK ST.chars SW.W = true := by quickRfl

theorem kSizes : (Li.length == 8 && Ls.length == 2) = true := by decide +kernel

theorem kBase : Li.all (fun w => w.all fun z => decide (0 ≤ z) && decide (z.toNat < 20)) = true := by
  decide +kernel

theorem kSl : Ls.all (fun w => w.all fun z => z != 0 && decide (z.natAbs ≤ 8)) = true := by
  decide +kernel

theorem kInv : CFSG.KLie.CT.allN 8 (fun k => Nat.beq (mulF 24 (lget Ims k) (lget ImsI k)) (idF 24)) =
    true := by
  quickRfl

theorem kRel : co1Spec.rels.all (fun r => r.all (fun l => decide (l.1 < 8)) &&
    Nat.beq (wordRF 24 (imgF Ims ImsI) (r.map letterOf)) (idF 24)) = true := by quickRfl

theorem kSA : Nat.beq (wordRF 24 (imgF Ims ImsI) (Ls.getD 0 [])) CertificateChecks.KernelVec.Co1.NA =
    true := by quickRfl

theorem kSB : Nat.beq (wordRF 24 (imgF Ims ImsI) (Ls.getD 1 [])) CertificateChecks.KernelVec.Co1.NB =
    true := by quickRfl

end CertificateChecks.KernelCo1Surj

end
