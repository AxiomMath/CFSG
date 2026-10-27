module

public import CFSG.ClassicalInvolution.Phan.Phan3B3CTData
import Certificates.Kernel.PhanB3.SGGlue
public import CFSG.ClassicalInvolution.Phan.Phan3AModel
public import CFSG.ClassicalInvolution.Phan.Phan3B3TwistData
public import CFSG.ClassicalInvolution.Phan.Phan3D4Defs

public section

namespace Certificates

open CertificateChecks

open CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.CosetTable CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.ClassicalInvolution.Phan.Q3G in
theorem certificate270007 :
    (Finite PhanB3Group ∧ Nat.card PhanB3Group ≤ 176904 * 51840) ∧
      (∃ N : Subgroup PhanB3Group, N.Normal ∧ Nat.card N ≤ 2 ∧
        (∀ w ∈ b3Sl3EdgeRels ++ b3Sp4EdgeRels ++ b3CtCommRels, wordVal b3CtEltP w ∈ N) ∧
        ∀ i : Fin 8,
          (wordVal b3CtEltP (decodeWord 6 b3PhanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i ∈ N) ∧
      (∀ p ∈ b3BadPairs, Subsingleton (PG 6 (b3TwistRels p.1 p.2))) ∧
      (Finite (PG 4 sl3Rels) ∧ Nat.card (PG 4 sl3Rels) ≤ 5616) ∧
      (Finite (PG 4 sp4Rels) ∧ Nat.card (PG 4 sp4Rels) ≤ 51840) := by
  have hct : KernelPhanB3.ctElt = b3CtEltP := rfl
  refine ⟨KernelPhanB3.card_le, ?_, fun p hp => ?_, KernelPhanB3.card_sl3,
    KernelPhanB3.card_sp4⟩
  · rw [← hct]
    exact KernelPhanB3.ker_facts
  · have := (KernelPhanB3.card_twist p hp).1
    exact Finite.card_le_one_iff_subsingleton.1 (KernelPhanB3.card_twist p hp).2

end Certificates
