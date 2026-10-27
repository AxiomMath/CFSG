module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA3

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure KData (K V₀ : Subgroup G) (c : G) : Prop where
  c3 : c ^ 3 = 1
  cne : c ≠ 1
  V_le : V₀ ≤ K
  V_card : Nat.card V₀ = 4
  V_sq : ∀ v ∈ V₀, v * v = 1
  V_cen : ∀ v ∈ V₀, ∀ k ∈ K, v * k = k * v
  V_norm : ∀ v ∈ V₀, c * v * c⁻¹ ∈ V₀
  V_comm : ∀ v ∈ V₀, ∃ w ∈ V₀, v = w * (c * w * c⁻¹)
  K_dec : ∀ k ∈ K, ∃ v ∈ V₀, ∃ z ∈ K, z * c = c * z ∧ k = v * z

namespace ConfR

open SFourC

variable {δ μ : Geo H M} {U T C : Subgroup G}

theorem kData (hA : F53Amalgam H M S) (h : ConfR δ μ U) (hS : SFourC U T C)
    (eT : ↥T ≃* Perm (Fin 4)) {c₀ : Perm (Fin 4)} (h3 : c₀ ^ 3 = 1) (h1 : c₀ ≠ 1) :
    KData (Qv δ) ((klein4).map (tau eT)) (tau eT c₀) := by
  have hKR : Qv δ ≤ pCoreOf 2 U := h.sig.inf_Qv_le_R.trans' (le_inf (h.hQδ.trans h.hQ) le_rfl)
  have hVK := klein4_le_Qv hA h hS eT
  have hcen : ∀ w ∈ klein4, ∀ k ∈ Qv δ, tau eT w * k = k * tau eT w := by
    intro w hw k hk
    obtain ⟨w', hw', z, hz, rfl⟩ := R_le_VC hS eT (hKR hk)
    have h1 : tau eT w * tau eT w' = tau eT w' * tau eT w := by
      rw [← map_mul, ← map_mul, klein4_comm w hw w' hw']
    have h2 : tau eT w * z = z * tau eT w := hS.comm _ (tau_mem eT w) z hz
    calc tau eT w * (tau eT w' * z) = (tau eT w * tau eT w') * z := by group
      _ = tau eT w' * (tau eT w * z) := by rw [h1]; group
      _ = tau eT w' * (z * tau eT w) := by rw [h2]
      _ = tau eT w' * z * tau eT w := by group
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h3, map_one]
  · intro h1'
    exact h1 (tau_injective eT (h1'.trans (map_one _).symm))
  · rintro _ ⟨w, hw, rfl⟩
    exact hVK w hw
  · rw [Subgroup.card_map_of_injective (tau_injective eT), card_klein4]
  · rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul]
    have := (mem_klein4.mp hw).1
    rw [← sq, this, map_one]
  · rintro _ ⟨w, hw, rfl⟩ k hk
    exact hcen w hw k hk
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨c₀ * w * c₀⁻¹, klein4_normal.conj_mem w hw c₀, ?_⟩
    simp
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨w', hw', hww'⟩ := klein4_eq_comm_of_three c₀ h3 h1 w hw
    refine ⟨tau eT w', ⟨w', hw', rfl⟩, ?_⟩
    rw [hww']
    simp [map_mul, map_inv]
  · intro k hk
    obtain ⟨w, hw, z, hz, rfl⟩ := R_le_VC hS eT (hKR hk)
    refine ⟨tau eT w, ⟨w, hw, rfl⟩, z, ?_, ?_, rfl⟩
    · have := Subgroup.mul_mem _ (Subgroup.inv_mem _ (hVK w hw)) hk
      simpa using this
    · exact (hS.comm _ (tau_mem eT _) z hz).symm

theorem exists_q0 (h : ConfR δ μ U) (hS : SFourC U T C) (eT : ↥T ≃* Perm (Fin 4)) :
    ∃ q ∈ pCoreOf 2 U, q ∉ Qv δ ∧ ∃ w ∈ klein4, ∃ z ∈ C, q = tau eT w * z := by
  obtain ⟨q, hq, hqK⟩ := Set.not_subset.mp h.hR
  obtain ⟨w, hw, z, hz, hqe⟩ := R_le_VC hS eT hq
  exact ⟨q, hq, hqK, w, hw, z, hz, hqe⟩

end ConfR

end CFSG.Quasithin.F53
