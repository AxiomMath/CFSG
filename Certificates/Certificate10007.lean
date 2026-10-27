module

public import CFSG.LieType.Multipliers.Sz8Inputs
import Certificates.Kernel.Multipliers.Sz8Upper
import Certificates.Kernel.Misc.Coset.C10007M

public section

namespace Certificates

open CertificateChecks

open CFSG.LieType CFSG.LieType.Multipliers CFSG.LieType.Multipliers.Sz8 TauCeti CFSG.CosetTable in
theorem certificate10007 :
    (matCheck [CFSG.LieType.Multipliers.Sz8.wWord 0 ++ [(0, false)], CFSG.LieType.Multipliers.Sz8.wWord 1 ++ [(1, false)]] = true)
    ∧ (Finite (PG 2 (coverWords rels CFSG.LieType.Multipliers.Sz8.wWord)) ∧ Nat.card (PG 2 (coverWords rels CFSG.LieType.Multipliers.Sz8.wWord)) ≤ 116480)
    ∧ ∀ u, (u, 2) ∈ kerWords →
      2 ∣ orderOf (PresentedGroup.mk (wordSet (coverWords rels CFSG.LieType.Multipliers.Sz8.wWord)) (FreeGroup.mk u)) :=
  ⟨KernelMiscCoset.C10007.matCheck_wWord, KernelSz8.card_le, KernelSz8.two_dvd⟩

end Certificates
