module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec2

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

private theorem he42zm_fin_left : ∀ g : GL2, g ^ 3 = 1 → ∀ M : M2,
    (g : M2) * ((g : M2) * M + M) = ((g : M2) * M + M) * (g : M2) →
      (g : M2) * M = M * (g : M2) := by
  decide +kernel

private theorem he42zm_fin_right : ∀ g : GL2, g ^ 3 = 1 → ∀ M : M2,
    (g : M2) * (M * (g : M2)ᵀ + M) = (M * (g : M2)ᵀ + M) * (g : M2) →
      (g : M2) * M = M * (g : M2) := by
  decide +kernel

private theorem he42zm_fin_conj : ∀ g : GL2, g ^ 3 = 1 → g ≠ 1 →
    (g : M2) * (!![0, 1; 1, 0] : M2) * ((g⁻¹ : GL2) : M2)ᵀ ≠ (!![0, 1; 1, 0] : M2) := by
  decide +kernel

private theorem he42zm_m_conj (S : HeSetup G) {y : G} (hy : y ∈ S.N) {z : G} (hz : z ∈ S.Z) :
    S.m (y * z * y⁻¹) = ((S.rhoG y).1 : M2) * S.m z * ((S.rhoG y).2 : M2)ᵀ := by
  rw [S.rhoG_of_mem hy]
  exact S.hD.hT.m_conj S.N S.hD.hK.norm ⟨y, hy⟩ hz

theorem HeSetup.stepZmat (S : HeSetup G) (hB : S.BaseFacts) {y₁ y₂ : G} (hY : YSpec S y₁ y₂) :
    S.StepZmat y₁ y₂ := by
  have g3 : S.g ^ 3 = 1 := S.hD.g_pow_three S.hxN S.hxa S.hx3
  have g1 : S.g ≠ 1 := S.hD.g_ne_one S.hxN S.hxa S.hx3
  have hy0N : y₁ * y₂⁻¹ ∈ S.N := S.N.mul_mem hY.mem₁ (S.N.inv_mem hY.mem₂)
  have hρ0 : S.rhoG (y₁ * y₂⁻¹) = (S.g, S.g⁻¹) := by
    have h : S.rhoG (y₁ * y₂⁻¹) = S.rhoG y₁ * (S.rhoG y₂)⁻¹ := by
      rw [S.rhoG_of_mem hy0N, S.rhoG_of_mem hY.mem₁, S.rhoG_of_mem hY.mem₂, ← map_inv,
        ← map_mul]
      rfl
    rw [h, hY.rho₁, hY.rho₂]
    exact Prod.ext (by simp) (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hy z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact S.hD.mem_Z_conj hY.mem₁ hz
    · exact S.hD.mem_Z_conj hY.mem₂ hz
    · exact S.hD.mem_Z_conj hy0N hz
  · intro z hz hB'
    have hB0 : y₁ * z * y₁⁻¹ * z⁻¹ ∈ (S.A ⊓ S.A') ⊓ centralizer ({S.x} : Set G) := hB'
    have hw : y₁ * z * y₁⁻¹ ∈ S.A ⊓ S.A' := S.hD.mem_Z_conj hY.mem₁ hz
    have hzi : z⁻¹ ∈ S.A ⊓ S.A' := inv_mem hz
    have hmul : S.m (y₁ * z * y₁⁻¹ * z⁻¹) = S.m (y₁ * z * y₁⁻¹) + S.m z := by
      rw [S.hD.hT.mmul _ hw _ hzi, S.hD.hT.m_inv hz]
    have hc : S.m (y₁ * z * y₁⁻¹) = (S.g : M2) * S.m z := by
      rw [he42zm_m_conj S hY.mem₁ hz, hY.rho₁]
      simp
    have hcomm := ((S.hD.mem_B_iff S.hxN S.hxa S.hx3).1 hB0).2
    rw [hmul, hc] at hcomm
    show z ∈ (S.A ⊓ S.A') ⊓ centralizer ({S.x} : Set G)
    exact (S.hD.mem_B_iff S.hxN S.hxa S.hx3).2 ⟨hz, he42zm_fin_left S.g g3 (S.m z) hcomm⟩
  · intro z hz hB'
    have hB0 : y₂ * z * y₂⁻¹ * z⁻¹ ∈ (S.A ⊓ S.A') ⊓ centralizer ({S.x} : Set G) := hB'
    have hw : y₂ * z * y₂⁻¹ ∈ S.A ⊓ S.A' := S.hD.mem_Z_conj hY.mem₂ hz
    have hzi : z⁻¹ ∈ S.A ⊓ S.A' := inv_mem hz
    have hmul : S.m (y₂ * z * y₂⁻¹ * z⁻¹) = S.m (y₂ * z * y₂⁻¹) + S.m z := by
      rw [S.hD.hT.mmul _ hw _ hzi, S.hD.hT.m_inv hz]
    have hc : S.m (y₂ * z * y₂⁻¹) = S.m z * (S.g : M2)ᵀ := by
      rw [he42zm_m_conj S hY.mem₂ hz, hY.rho₂]
      simp
    have hcomm := ((S.hD.mem_B_iff S.hxN S.hxa S.hx3).1 hB0).2
    rw [hmul, hc] at hcomm
    show z ∈ (S.A ⊓ S.A') ⊓ centralizer ({S.x} : Set G)
    exact (S.hD.mem_B_iff S.hxN S.hxa S.hx3).2 ⟨hz, he42zm_fin_right S.g g3 (S.m z) hcomm⟩
  · obtain ⟨z, hz, hzs⟩ := S.hD.hT.msurj (!![0, 1; 1, 0] : M2)
    refine ⟨z, hz, fun h => ?_⟩
    have h1 := congrArg S.m h
    rw [he42zm_m_conj S hy0N hz, hρ0, hzs] at h1
    dsimp only at h1
    exact he42zm_fin_conj S.g g3 g1 h1

end CFSG.Quasithin.A94.He42
