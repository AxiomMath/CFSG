module

public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

theorem E7LeviData.map {G G' : Type} [Group G] [Group G'] (φ : G →* G')
    (hφ : Function.Injective φ) {L P J D : Subgroup G} {σ b : G} (h : E7LeviData L σ b P J D) :
    E7LeviData (L.map φ) (φ σ) (φ b) (P.map φ) (J.map φ) (D.map φ) := by
  refine ⟨Subgroup.mem_map_of_mem φ h.σ_mem, Subgroup.map_mono h.P_le, h.P_two.map φ,
    ?_, ?_, ?_, Subgroup.map_mono h.J_le, ?_, Subgroup.map_mono h.D_le,
    (Subgroup.map_mono h.D_norm).trans (Subgroup.le_normalizer_map φ), ?_,
    Subgroup.mem_map_of_mem φ h.b_mem, ?_⟩
  · intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    simpa only [MonoidHom.map_zpowers, map_mul, map_inv] using
      Subgroup.mem_map_of_mem φ (h.P_comm x' hx' y' hy')
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    simpa only [map_mul] using congrArg φ (h.P_cent x' hx')
  · intro x hx hcomm
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [← MonoidHom.map_zpowers φ σ]
    apply Subgroup.mem_map_of_mem
    apply h.centP x' hx'
    intro y hy
    exact hφ (by simpa only [map_mul] using hcomm (φ y) (Subgroup.mem_map_of_mem φ hy))
  · intro x hx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    simpa only [map_mul] using congrArg φ (h.J_cent x' hx')
  · rcases h.D_SL with ⟨e⟩
    exact ⟨(Subgroup.equivMapOfInjective D φ hφ).symm.trans e⟩
  · exact (orderOf_injective φ hφ b).trans h.b_ord

theorem E7ModuleData.map {G G' : Type} [Group G] [Group G'] (φ : G →* G')
    (hφ : Function.Injective φ) {U L P : Subgroup G} {t₀ σ : G}
    (h : E7ModuleData U t₀ σ L P) :
    E7ModuleData (U.map φ) (φ t₀) (φ σ) (L.map φ) (P.map φ) := by
  have hmodW : modW (U.map φ) (φ t₀) (φ σ) = (modW U t₀ σ).map φ := by
    simp only [modW, Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.map_sup]
  refine ⟨Subgroup.mem_map_of_mem φ h.t₀_mem, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    simpa only [MonoidHom.map_zpowers, map_mul, map_inv] using
      Subgroup.mem_map_of_mem φ (h.U_comm x' hx' y' hy')
  · intro x hx w hw
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    rw [hmodW] at hw
    obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
    simpa only [MonoidHom.map_zpowers, map_mul, map_inv] using
      Subgroup.mem_map_of_mem φ (h.P_W x' hx' w' hw')
  · intro x hx hxU hxW
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have hxU' : φ (x' * σ * x'⁻¹ * σ⁻¹) ∈ U.map φ := by
      simpa only [map_mul, map_inv] using hxU
    rw [Subgroup.mem_map_iff_mem hφ] at hxU'
    apply Subgroup.mem_map_of_mem
    apply h.L_W x' hx' hxU'
    intro w hw
    have hmem : φ w ∈ modW (U.map φ) (φ t₀) (φ σ) := by
      rw [hmodW]
      exact Subgroup.mem_map_of_mem φ hw
    have hcomm : φ (x' * w * x'⁻¹ * w⁻¹) ∈ Subgroup.zpowers (φ t₀) := by
      simpa only [map_mul, map_inv] using hxW (φ w) hmem
    rwa [← MonoidHom.map_zpowers φ t₀, Subgroup.mem_map_iff_mem hφ] at hcomm

end CFSG.StandardType.FrameRoute.FS81

end
