module

public import CFSG.Sporadic.Bridge.VecSurj
public import Certificates.Data.GMS78RuAsmNA
import Certificates.Kernel.GMS78.Coset.Cards
import Certificates.Kernel.GMS78.W106
import Certificates.Kernel.GMS78.W106M

public section

namespace Certificates

open CertificateChecks

open CFSG in
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.VecSurj CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm in
theorem certificate15106 : (Finite (CFSG.CosetTable.PG ruSub2.length ruRels2) ∧
      Nat.card (CFSG.CosetTable.PG ruSub2.length ruRels2) ≤ 344064)
    ∧ (CFSG.ComponentClassification.GMS78.RuAsm.ruNACheckModel = true)
    ∧ ∀ k < 7, wordProd (img pi7RuSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
      (ruAsmNatWord (ruA0PowWord (k + 1))) ≠ 1 :=
  ⟨KernelGMS78.Coset.card_P2, KernelGMS78.ruNACheckModel_ok, KernelGMS78.W.a0_ne⟩

end Certificates
