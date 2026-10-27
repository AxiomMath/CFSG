module

public import Certificates.Kernel.Co2I301.SixData
public import Certificates.Data.Kernel.Co2I301.Six
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2I301

open CFSG.KC.Enum CFSG.KC.Co2I301

@[expose] noncomputable def PI (g : Nat) : Nat := SX.pi.getD g 0

@[expose] noncomputable def PII (g : Nat) : Nat := SX.pii.getD g 0

@[expose] noncomputable def HL (t : Nat) : Nat := SX.hl.getD t 0

@[expose] noncomputable def HLI (t : Nat) : Nat := SX.hli.getD t 0

@[expose] noncomputable def TG (h : Nat) : Nat := SX.tg.getD h 0

@[expose] noncomputable def FK (g : Nat) : Nat := nIf(Nat.beq g (nat_lit 0), SX.fk1, SX.fk2)

@[expose] noncomputable def AU (u : Nat) : Nat :=
  cp (pw SX.fd (Nat.mod u (nat_lit 3))) (pw SX.fs (Nat.div u (nat_lit 3)))

theorem o_ok : allN 672 (oRec OR 672 SX.fd PI PII) = true := by quickRfl

theorem k_ok : allN 360 (kRec KR 360 FK) = true := by quickRfl

theorem l_ok : allN 2160 (lRec LR 2160 KR 360 AU SX.fk1 SX.fk2) = true := by quickRfl

theorem t_ok : allN 512 (tRec TR 512 TG SR 5103) = true := by quickRfl

theorem s_ok : allN 5103 (sRec SR 5103 PI PII HL HLI) = true := by quickRfl

theorem inv_ok : (inv63 (PI 0) (PII 0) && inv63 (PI 1) (PII 1) && inv63 (HL 0) (HLI 0) &&
    inv63 (HL 1) (HLI 1) && inv63 (HL 2) (HLI 2)) = true := by quickRfl

theorem tg_ok : allN 4 (fun h => Nat.beq (TG h) (wP PI PII (SX.tgw.getD h []))) = true := by
  quickRfl

theorem tw_ok : ∀ h < 4, ∀ c ∈ SX.tgw.getD h [], c < 4 := by decide

theorem troot : Nat.beq (cd (TR 511)) idc = true := by quickRfl

end CertificateChecks.KernelCo2I301

end
