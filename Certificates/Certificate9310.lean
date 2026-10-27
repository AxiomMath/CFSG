module

public import CFSG.Sporadic.Ly.Setup
public import CFSG.Open.Defs
import CFSG.ClassicalInvolution.SmallCases.Sporadic.LyAssembly

public section

open CFSG.ClassicalInvolution.LyProof

namespace Certificates

open CFSG.Sporadic.Ly in
theorem certificate9310 : ∃ _ : LySeed, ∃ z : CFSG.Sporadic.Ly.J, ∃ K S : Subgroup CFSG.Sporadic.Ly.J, z * z = 1 ∧ z ≠ 1 ∧
    Subgroup.centralizer ({z} : Set CFSG.Sporadic.Ly.J) = K ∧ CFSG.Open.IsQuasisimple K ∧
    Nat.card (Subgroup.center K) = 2 ∧ Nat.card K = 39916800 ∧
    IsPGroup 2 S ∧ ¬ 2 ∣ S.index ∧ Nat.card S = 256 ∧
    (∀ s ∈ S, s * s = 1 → s ≠ 1 → ∃ C : CFSG.Sporadic.Ly.J, s = C * z * C⁻¹) ∧
    ∃ u ∈ K, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z := by
  have hidx : ¬ 2 ∣ SJ.index := by
    have h := S_sylow.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at h
  obtain ⟨hcen, hqs, hz, hK⟩ := K_facts
  obtain ⟨hS, hfus⟩ := S_facts
  exact ⟨inferInstance, zJ, KJ, SJ, z_facts.1, z_facts.2, hcen, hqs, hz, hK, S_sylow.1, hidx, hS,
    hfus, exists_noncentral_involution⟩

end Certificates
