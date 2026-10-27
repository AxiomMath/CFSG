module

public import Certificates.Kernel.B45.C260394D
public import Certificates.Kernel.Misc.RuSq.Chain
public import Certificates.Data.Kernel.B45Perm.RuSyl

public section

namespace CertificateChecks.KernelB45.C260394

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.B45P.RuSyl CertificateChecks.KernelMisc

@[expose] noncomputable def covB (q : Nat) : Bool :=
  strictB (RuSqS.LR 0) (fun R0 => strictB (RuSqS.LR 1) (fun R1 =>
  strictB (roff 4060 48720 R0) (fun o0 => strictB (roff 4060 48720 R1) (fun o1 =>
    allN 256 (fun d => covC R0 R1 RuSqS.TR RuSqS.TRI CD IX o0 o1 (Nat.add (Nat.mul 256 q) d))))))

@[expose] noncomputable def invB : Bool :=
  strictB (roff 4060 48720 (RuSqS.LR 0)) (fun o0 => strictB (roff 4060 48720 (RuSqS.LR 1))
    (fun o1 => allN 495 (fun i => invC RuSqS.TR CD IX K0 K1 o0 o1 i)))

@[expose] noncomputable def rowB (q : Nat) : Bool :=
  strictB (roff 4060 48720 (RuSqS.LR 0)) (fun o0 => strictB (roff 4060 48720 (RuSqS.LR 1))
    (fun o1 => allN 15 (fun d => rowC RuSqS.TR CD K0 K1 CM PR o0 o1 (Nat.add (Nat.mul 15 q) d))))

end CertificateChecks.KernelB45.C260394

end
