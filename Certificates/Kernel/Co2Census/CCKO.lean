module

public import Certificates.Kernel.Co2Census.CCXDefs
public import Certificates.Kernel.Co2Census.HPData
public import Certificates.Kernel.Co2Census.CCData
public import CFSG.Certificates.Kernel.Common.Cover
public import Certificates.Kernel.Co2Census.CCDefs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo2Census

open CFSG.KC.Co2InvS CFSG.KC.Co2Census CFSG.KC.Loop

@[expose] noncomputable def o1G (l : Nat) : Nat := if l < 512 then QKt l else C26805GRt (l - 512)

@[expose] noncomputable def o1GI (l : Nat) : Nat :=
  if l < 512 then QKt (QIt l) else C26805GIt (l - 512)

theorem QI_ok : ∀ e < 512, (Nat.blt (QIt e) 512 && Nat.beq (mulV (QKt e) (QKt (QIt e))) IDP) =
    true := by
  kc_cover 128

theorem C26805GI_ok : (List.range 3).all (fun l => Nat.beq (mulV (C26805GRt l) (C26805GIt l)) IDP &&
    Nat.blt (C26805GIt l) (2 ^ 484)) = true := by
  decide +kernel

theorem O1_clos : ∀ k < 8240, (letB (k / 16) fun l => letB (k % 16) fun i =>
    Nat.blt (O1Ct k) 16 && Nat.beq (mulV (mulV (o1G l) (O1t i)) (o1GI l)) (O1t (O1Ct k))) =
      true := by
  kc_cover 1030

theorem O1_misc : (Nat.beq (O1t 0) (mulV (SK 26805) (QKt 0)) && (List.range 16).all fun i =>
    Nat.blt (O1t i) (2 ^ 484) && !Nat.beq (O1t i) (mulV (SK 26805) (QKt 32))) = true := by
  decide +kernel

end CertificateChecks.KernelCo2Census
