module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA14
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA13

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

open SFourC

variable {δ μ : Geo H M} {U T C : Subgroup G}

theorem conj_mem_map_tau (eT : ↥T ≃* Perm (Fin 4)) {t : G} (ht : t ∈ T) {w : Perm (Fin 4)}
    (hw : w ∈ klein4) : t * tau eT w * t⁻¹ ∈ (klein4).map (tau eT) := by
  refine ⟨eT ⟨t, ht⟩ * w * (eT ⟨t, ht⟩)⁻¹, klein4_normal.conj_mem w hw _, ?_⟩
  rw [map_mul, map_mul, map_inv, mem_T_eq eT t ht]

theorem pCoreOf_T (eT : ↥T ≃* Perm (Fin 4)) : pCoreOf 2 T = (klein4).map (tau eT) := by
  apply le_antisymm
  · intro x hx
    have hxT : x ∈ T := CFSG.LieType.BorelTits.pCoreOf_le 2 T hx
    set N' : Subgroup (Perm (Fin 4)) := (pCoreOf 2 T).comap (tau eT) with hN'
    have hnorm : N'.Normal := by
      refine ⟨fun y hy g => ?_⟩
      have hy' : tau eT y ∈ pCoreOf 2 T := hy
      show tau eT (g * y * g⁻¹) ∈ pCoreOf 2 T
      rw [map_mul, map_mul, map_inv]
      have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 T (tau_mem eT g)
      exact (Subgroup.mem_normalizer_iff.mp this _).mp hy'
    have hp : IsPGroup 2 N' := by
      intro y
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) T ⟨tau eT y, y.2⟩
      refine ⟨k, Subtype.ext (tau_injective eT ?_)⟩
      have := congrArg Subtype.val hk
      simpa using this
    have h1 := normal2_le_klein4 hp
    have hx' : eT ⟨x, hxT⟩ ∈ N' := by
      show tau eT (eT ⟨x, hxT⟩) ∈ pCoreOf 2 T
      rw [mem_T_eq eT x hxT]; exact hx
    exact ⟨_, h1 hx', mem_T_eq eT x hxT⟩
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · rintro _ ⟨w, -, rfl⟩; exact tau_mem eT w
    · intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨w, hw, rfl⟩; exact conj_mem_map_tau eT ht hw
      · intro hy
        obtain ⟨w, hw, hwe⟩ := hy
        have := conj_mem_map_tau (T := T) eT (T.inv_mem ht) hw
        have e : t⁻¹ * tau eT w * t⁻¹⁻¹ = y := by rw [hwe]; group
        rwa [e] at this
    · rintro ⟨_, w, hw, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      show tau eT w ^ 2 ^ 1 = 1
      rw [← map_pow]
      simp [(mem_klein4.mp hw).1]

theorem normalizer_C (hS : SFourC U T C) : U ≤ Subgroup.normalizer (C : Set G) := by
  have key : ∀ g ∈ U, ∀ y ∈ C, g * y * g⁻¹ ∈ C := by
    intro g hg y hy
    obtain ⟨t, ht, z, hz, rfl⟩ := mem_sup_of_commute hS.comm (hS.sup ▸ hg)
    have hzy : z * y * z⁻¹ ∈ C := C.mul_mem (C.mul_mem hz hy) (C.inv_mem hz)
    have h1 := hS.comm t ht _ hzy
    have e : t * z * y * (t * z)⁻¹ = z * y * z⁻¹ := by
      calc t * z * y * (t * z)⁻¹ = t * (z * y * z⁻¹) * t⁻¹ := by group
        _ = (z * y * z⁻¹ * t) * t⁻¹ := by rw [h1]
        _ = z * y * z⁻¹ := by group
    rw [e]; exact hzy
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (U.inv_mem hg) _ hy
  simpa [mul_assoc] using this

theorem A2 (hA : F53Amalgam H M S) (h : ConfR δ μ U) {T C : Subgroup G} (hS : SFourC U T C) :
    Nat.card (pCoreOf 2 T) = 4 ∧ IsElemAbelian 2 (pCoreOf 2 T) ∧
      pCoreOf 2 U = pCoreOf 2 T ⊔ C ∧ Qv μ = (T ⊓ Qv μ) ⊔ C ∧ pCoreOf 2 T ≤ Qv δ ∧
      Qv δ = pCoreOf 2 T ⊔ (C ⊓ Qv δ) ∧ (C ⊓ Qv δ).relIndex C = 2 ∧
      (∃ c ∈ T, orderOf c = 3) ∧
      (∀ c ∈ T, orderOf c = 3 →
        ⁅Qv δ, Subgroup.zpowers c⁆ = pCoreOf 2 T ∧
          ⁅pCoreOf 2 U, Subgroup.zpowers c⁆ = pCoreOf 2 T) ∧
      Qv μ ⊓ Subgroup.centralizer (pCoreOf 2 T : Set G) = pCoreOf 2 U := by
  obtain ⟨eT⟩ := hS.perm
  obtain ⟨ψ, hψs, hker⟩ := h.exists_psi hA
  have hV := pCoreOf_T eT
  have hX : stab δ ≤ Subgroup.normalizer ((Qv δ : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (stab δ)
  have hKR : Qv δ ≤ pCoreOf 2 U := h.sig.inf_Qv_le_R.trans' (le_inf (h.hQδ.trans h.hQ) le_rfl)
  have hRP : pCoreOf 2 U ≤ Qv μ := fun x hx => (h.sig.R_le_P hx).1
  have hVK := klein4_le_Qv hA h hS eT
  have hVKsub : pCoreOf 2 T ≤ Qv δ := by
    rw [hV]; rintro _ ⟨w, hw, rfl⟩; exact hVK w hw
  have hCR : C ≤ pCoreOf 2 U :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hS.le_C (normalizer_C hS) hS.pgrp
  have hR : pCoreOf 2 U = pCoreOf 2 T ⊔ C := by
    refine le_antisymm (fun x hx => ?_) (sup_le (hVKsub.trans hKR) hCR)
    obtain ⟨w, hw, z, hz, rfl⟩ := R_le_VC hS eT hx
    rw [hV]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨w, hw, rfl⟩) (Subgroup.mem_sup_right hz)
  have hCP : C ≤ Qv μ := hCR.trans hRP
  refine ⟨?_, ?_, hR, ?_, hVKsub, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV, Subgroup.card_map_of_injective (tau_injective eT), card_klein4]
  · rw [hV]
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨_, ⟨w, hw, rfl⟩⟩ := a
      obtain ⟨_, ⟨w', hw', rfl⟩⟩ := b
      show tau eT w * tau eT w' = tau eT w' * tau eT w
      rw [← map_mul, ← map_mul, klein4_comm w hw w' hw']
    · obtain ⟨w, hw, rfl⟩ := hx
      rw [← map_pow, (mem_klein4.mp hw).1, map_one]
  · apply le_antisymm
    · intro x hx
      obtain ⟨t, ht, z, hz, rfl⟩ := mem_sup_of_commute hS.comm (hS.sup ▸ h.hQ hx)
      have hzP : z ∈ Qv μ := hCP hz
      have htP : t ∈ Qv μ := by
        have := (Qv μ).mul_mem hx ((Qv μ).inv_mem hzP)
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨ht, htP⟩) (Subgroup.mem_sup_right hz)
    · exact sup_le inf_le_right hCP
  · apply le_antisymm
    · intro k hk
      obtain ⟨w, hw, z, hz, rfl⟩ := R_le_VC hS eT (hKR hk)
      have hzK : z ∈ Qv δ := by
        have := (Qv δ).mul_mem ((Qv δ).inv_mem (hVK w hw)) hk
        simpa using this
      rw [hV]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨w, hw, rfl⟩)
        (Subgroup.mem_sup_right ⟨hz, hzK⟩)
    · exact sup_le hVKsub inf_le_right
  ·
    have hCN : C ≤ Subgroup.normalizer ((Qv δ : Subgroup G) : Set G) :=
      hS.le_C.trans (h.sig.le_stab.trans hX)
    have hKC : Qv δ ⊔ C = pCoreOf 2 U :=
      le_antisymm (sup_le hKR hCR) (by rw [hR]; exact sup_le_sup_right hVKsub C)
    have h1 := F53Push.relIndex_sup_eq_relIndex_inf_right hCN
    rw [hKC, inf_comm] at h1
    rw [← h1]
    have h2 := Subgroup.relIndex_mul_card (Qv δ) (pCoreOf 2 U)
    rw [inf_of_le_left hKR, h.card_R_K hA] at h2
    have hpos : 0 < Nat.card (Qv δ) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  · obtain ⟨c₀, hc₀3, hc₀1⟩ : ∃ c₀ : Perm (Fin 4), c₀ ^ 3 = 1 ∧ c₀ ≠ 1 :=
      ⟨cyc4, cyc4_pow_three, cyc4_ne_one⟩
    refine ⟨tau eT c₀, tau_mem eT c₀, ?_⟩
    rw [orderOf_injective (tau eT) (tau_injective eT), orderOf_eq_prime hc₀3 hc₀1]
  · intro c hcT hc3
    set c₀ := eT ⟨c, hcT⟩ with hc₀
    have hce : tau eT c₀ = c := mem_T_eq eT c hcT
    have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
    have hc₀3 : c₀ ^ 3 = 1 := by
      apply tau_injective eT
      rw [map_pow, hce, map_one]
      exact hc3'
    have hc₀1 : c₀ ≠ 1 := by
      intro h1
      rw [h1, map_one] at hce
      have : orderOf c = 1 := by rw [← hce]; exact orderOf_one
      omega
    have hKd := h.kData hA hS eT hc₀3 hc₀1
    rw [hce] at hKd
    have hcX : c ∈ stab δ := h.sig.le_stab (hS.le_T hcT)
    refine ⟨?_, ?_⟩
    · rw [hV]
      exact commutator_K_c hX hKd ψ hψs hker hcX
    · rw [hV]
      refine le_antisymm ?_ ?_
      · rw [Subgroup.commutator_le]
        intro x hx t ht
        have htT : t ∈ T := (Subgroup.zpowers_le.mpr hcT) ht
        obtain ⟨w, hw, z, hz, rfl⟩ := R_le_VC hS eT hx
        have hzt : t * z = z * t := hS.comm t htT z hz
        have hmem := conj_mem_map_tau eT htT hw
        have hcalc : ⁅tau eT w * z, t⁆ = tau eT w * (t * tau eT w * t⁻¹)⁻¹ := by
          rw [commutatorElement_def]
          calc tau eT w * z * t * (tau eT w * z)⁻¹ * t⁻¹
              = tau eT w * (z * t * z⁻¹) * (tau eT w)⁻¹ * t⁻¹ := by group
            _ = tau eT w * (t * z * z⁻¹) * (tau eT w)⁻¹ * t⁻¹ := by rw [hzt]
            _ = _ := by group
        rw [hcalc]
        exact Subgroup.mul_mem _ ⟨w, hw, rfl⟩ (Subgroup.inv_mem _ hmem)
      · have := commutator_K_c hX hKd ψ hψs hker hcX
        rw [← this]
        exact Subgroup.commutator_mono hKR le_rfl
  · apply le_antisymm
    · rintro x ⟨hxP, hxC⟩
      have hxU : x ∈ U := h.hQ hxP
      obtain ⟨t, ht, z, hz, rfl⟩ := mem_sup_of_commute hS.comm (hS.sup ▸ hxU)
      have htC : ∀ v ∈ pCoreOf 2 T, v * t = t * v := by
        intro v hv
        have hvT : v ∈ T := CFSG.LieType.BorelTits.pCoreOf_le 2 T hv
        have h1 := Subgroup.mem_centralizer_iff.mp hxC v hv
        have h2 : v * z = z * v := hS.comm v hvT z hz
        have h3 : v * t * z = t * v * z := by
          calc v * t * z = v * (t * z) := by group
            _ = t * z * v := h1
            _ = t * (z * v) := by group
            _ = t * (v * z) := by rw [h2]
            _ = t * v * z := by group
        exact mul_right_cancel h3
      have htK : t ∈ (klein4).map (tau eT) := by
        refine ⟨eT ⟨t, ht⟩, centralizer_klein4 _ fun w hw => ?_, mem_T_eq eT t ht⟩
        apply tau_injective eT
        rw [map_mul, map_mul, mem_T_eq eT t ht]
        have := htC (tau eT w) (by rw [hV]; exact ⟨w, hw, rfl⟩)
        exact this.symm
      rw [hR, hV]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left htK) (Subgroup.mem_sup_right hz)
    · intro x hx
      refine ⟨hRP hx, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
      have hv' : v ∈ (klein4).map (tau eT) := hV ▸ hv
      obtain ⟨w, hw, rfl⟩ := hv'
      obtain ⟨w', hw', z, hz, rfl⟩ := R_le_VC hS eT hx
      have h1 : tau eT w * tau eT w' = tau eT w' * tau eT w := by
        rw [← map_mul, ← map_mul, klein4_comm w hw w' hw']
      have h2 : tau eT w * z = z * tau eT w := hS.comm _ (tau_mem eT w) z hz
      calc tau eT w * (tau eT w' * z) = (tau eT w * tau eT w') * z := by group
        _ = tau eT w' * (tau eT w * z) := by rw [h1]; group
        _ = tau eT w' * (z * tau eT w) := by rw [h2]
        _ = tau eT w' * z * tau eT w := by group

end ConfR

end CFSG.Quasithin.F53
