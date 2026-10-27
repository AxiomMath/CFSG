module

public import Certificates.Kernel.B45.C260394W
public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Data.Kernel.B45Perm.RuSylDbl
public import Certificates.Data.SmithB45ExcRuData
public import Certificates.Kernel.B45.C260394D
public import Certificates.Kernel.Misc.RuSq.Chain

public section

namespace CertificateChecks.KernelB45.C260394

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.B45P.RuSyl CertificateChecks.KernelMisc
  CertificateChecks.KernelSporSch.RuG CFSG.Quasithin.B45Exc.Ru

@[expose] noncomputable def wdOf (k : Nat) : List Int :=
  match ruDblWits[WI k]? with
  | some w => w.g
  | none => []

@[expose] noncomputable def dblB (q : Nat) : Bool :=
  bAnd(idK 4060 12 (mask 12), bAnd(gensTc 4060 12 [A0, A1] [A0I, A1I],
    strictB (pidn 4060 12) (fun idn =>
    strictB (roff 4060 48720 (RuSqS.LR 0)) (fun o0 => strictB (roff 4060 48720 (RuSqS.LR 1))
    (fun o1 => allN 12 (fun d =>
      bIf(Nat.blt (Nat.add (Nat.mul 12 q) d) (WN 0),
        dblC RuSqS.TR CD o0 o1 idn [A0, A1] [A0I, A1I] (quadC WQ (Nat.add (Nat.mul 12 q) d))
          (wdOf (Nat.add (Nat.mul 12 q) d)),
        true)))))))

end CertificateChecks.KernelB45.C260394

end
