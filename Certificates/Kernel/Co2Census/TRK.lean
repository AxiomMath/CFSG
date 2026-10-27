module

public import Certificates.Kernel.Co2Census.S0Defs
public import Certificates.Kernel.Co2SmithS.OrbK

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2SmithS CertificateChecks.KernelCo2SmithS
  CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def trOK (k : Nat) : Bool :=
  Nat.beq (TRt (trOff k)) IDP && (List.range (chainOrb[k]!)).all fun i => Nat.beq i 0 ||
    (Nat.blt (PI (k + 1) 0 i) i && Nat.blt (PI (k + 1) 1 i) ((chainGens ())[k]!).size &&
      Nat.beq (TRt (trOff k + i))
        (mulV (wK LT (((chainGens ())[k]!)[PI (k + 1) 1 i]!)) (TRt (trOff k + PI (k + 1) 0 i))))

theorem tr_ok : (List.range 6).all trOK = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
