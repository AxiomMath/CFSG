module

public import CFSG.Sporadic.Recognition.HNMult3Gens
public import CFSG.Sporadic.Recognition.HNMult3Words
import Certificates.Kernel.HN3.Facts
import Certificates.Kernel.CosetCC.C26963Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.HNMult3

open CFSG.CosetTable CFSG.Sporadic.Recognition.HNMult3 in
theorem certificate26963 :
    (
      ((∀ r ∈ hn3Rels, FreeGroup.lift gN (FreeGroup.mk r) = 1) ∧
        (∀ i, hn3Ord i = 0 → FreeGroup.lift gN (FreeGroup.mk (hn3Cw i)) = gN i) ∧
        (∀ i, hn3Ord i ≠ 0 → gN i ^ hn3Ord i = 1)) ∧
      58320 ≤ Nat.card Nsub) ∧
    (Finite (PG 3 hn3Cover) ∧ Nat.card (PG 3 hn3Cover) ≤ 58320) := by
  refine ⟨?_, KernelC26963.card_hn3Cover_le⟩
  have e : gN = KernelHN3.gU := by
    funext i
    unfold gN Rg KernelHN3.gU
    congr 1
    fin_cases i <;> rfl
  obtain ⟨hR, hw, hB, hc⟩ := KernelHN3.hn3_facts
  rw [Nsub, e]
  exact ⟨⟨hR, hw, hB⟩, hc⟩

end Certificates
