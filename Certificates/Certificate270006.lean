module

public import CFSG.ClassicalInvolution.Phan.Phan3D4Defs
import Certificates.Kernel.PhanD4Dce.Glue
import Certificates.Kernel.PhanD4Dce.Index
public import CFSG.ClassicalInvolution.Phan.Phan3AModel

public section

namespace Certificates

open CFSG.CosetTable CFSG.ClassicalInvolution.Phan.Q3G in
theorem certificate270006 :
    (Finite PhanD4Group ∧ Nat.card PhanD4Group ≤ 4 * 4952179814400) ∧
      (∃ N : Subgroup PhanD4Group, N.Normal ∧ Nat.card N ≤ 4 ∧
        (∀ w ∈ d4CtRels, wordVal ctEltP w ∈ N) ∧
        ∀ i : Fin 8,
          (wordVal ctEltP (decodeWord 8 phanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i ∈ N) ∧
      (Finite (PG 4 sl3Rels) ∧ Nat.card (PG 4 sl3Rels) ≤ 5616) := by
  have := certificate270005
  exact CFSG.KD.PhanD4Dce.certificate270006_of CFSG.KD.PhanD4Dce.index_phanR_le

end Certificates
