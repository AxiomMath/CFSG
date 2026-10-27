module

public import CFSG.Quasithin.EmptyFaithful.E22QWr
public import CFSG.Quasithin.EmptyFaithful.E22QLift

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b

theorem typeI_centralizes_z₁ {G : Type} [Group G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}
    (h : Wr p T M J₁ J₂ z₁) {g : G} (hgM : g ∈ M)
    (hgN : g ∈ Subgroup.normalizer (J₁ : Set G)) : g * z₁ = z₁ * g := by
  have hkey : ∀ x ∈ J₁, x ∈ M ↔ z₁ * x = x * z₁ := fun x hx => by
    have := SetLike.ext_iff.mp h.M_J₁ x
    simpa [Subgroup.mem_inf, hx, Subgroup.mem_centralizer_iff] using this
  have hyJ : g * z₁ * g⁻¹ ∈ J₁ := (Subgroup.mem_normalizer_iff.mp hgN z₁).mp h.z₁_mem
  have hcomm : ∀ x ∈ J₁, x * z₁ = z₁ * x → x * (g * z₁ * g⁻¹) = (g * z₁ * g⁻¹) * x := by
    intro x hxJ hxz
    have hxM : x ∈ M := (hkey x hxJ).mpr hxz.symm
    have hxM' : g⁻¹ * x * g ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hgM) hxM) hgM
    have hxJ' : g⁻¹ * x * g ∈ J₁ :=
      (Subgroup.mem_normalizer_iff.mp hgN _).mpr (by simpa [mul_assoc] using hxJ)
    have hc : z₁ * (g⁻¹ * x * g) = (g⁻¹ * x * g) * z₁ := (hkey _ hxJ').mp hxM'
    calc x * (g * z₁ * g⁻¹) = g * ((g⁻¹ * x * g) * z₁) * g⁻¹ := by group
      _ = g * (z₁ * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
      _ = (g * z₁ * g⁻¹) * x := by group
  rcases h.cen_fact _ hyJ hcomm with h1 | h1
  · exfalso
    have hz : z₁ = 1 := by
      have : z₁ = g⁻¹ * (g * z₁ * g⁻¹) * g := by group
      rw [h1] at this
      simpa using this
    have h2 := h.z₁_ord
    rw [hz, orderOf_one] at h2
    omega
  · exact mul_inv_eq_iff_eq_mul.mp h1

theorem typeI_aux {G : Type} [Group G] [Finite G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}
    (WL : WitnessL2 p) (h : Wr p T M J₁ J₂ z₁) {A : Subgroup G} (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A)
    (hR : T ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (J₁ : Set G))
    (hAD : ¬ A ≤ Subgroup.centralizer (J₁ : Set G)) :
    ∃ K : Subgroup G, E1.IsE 1 ⊤ T A K ∧ ¬ K ≤ M := by
  set R : Subgroup G := T ⊓ Subgroup.centralizer (A : Set G)
  set Q : Subgroup G := J₁ ⊔ R
  have hJN : J₁ ≤ Subgroup.normalizer (J₁ : Set G) := Subgroup.le_normalizer
  have hQN : Q ≤ Subgroup.normalizer (J₁ : Set G) := sup_le hJN hR
  have hDQ : J₁ ≤ Q := le_sup_left
  have hRQ : R ≤ Q := le_sup_right
  have hRT : R ≤ T := inf_le_left
  have hAR : A ≤ R :=
    le_inf hAT (Subgroup.le_centralizer_iff_isMulCommutative.mpr hAab.1)
  have hAQ : A ≤ Q := hAR.trans hRQ
  have hDn : (J₁.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDQ).mpr hQN
  have hRTQ : R ≤ T ⊓ Q := le_inf hRT hRQ
  have hQ : J₁ ⊔ (T ⊓ Q) = Q :=
    le_antisymm (sup_le hDQ inf_le_right) (sup_le_sup_left hRTQ J₁)
  have hTQN : T ⊓ Q ≤ Subgroup.normalizer (J₁ : Set G) := inf_le_right.trans hQN
  have hTQ2 : IsPGroup 2 ↥(T ⊓ Q) := h.sylow.isPGroup.to_le inf_le_left
  have hsyl : IsSylowIn 2 ((T ⊓ Q) ⊓ J₁) J₁ := by
    have : (T ⊓ Q) ⊓ J₁ = T ⊓ J₁ := by rw [inf_assoc, inf_eq_right.mpr hDQ]
    rw [this]
    exact h.sylow_J₁
  have hTQ : IsSylowIn 2 (T ⊓ Q) Q := by
    have := E1.isSylowIn_two_of_sup_inf hTQN hTQ2 hsyl
    rwa [hQ] at this
  have hτ : E1.tauOf ⊤ T A ≤ T ⊓ Q := by
    rw [h.tau_eq A]
    exact hRTQ
  have hzc : ∀ x ∈ T ⊓ Q, z₁ * x = x * z₁ := fun x hx => h.z₁_central x ⟨hx.1, hTQN hx⟩
  obtain ⟨J, hJQ, hJE, hJz⟩ := local_witness WL h.sylow hAT hAab hDQ hDn h.psl₁ h.simple₁
    h.nonab₁ hTQ hQ hτ hAQ hAD h.z₁_mem h.z₁_ord hzc
  refine ⟨J, hJE, fun hJM => hJz fun x hx => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  exact (typeI_centralizes_z₁ h (hJM hx) (hQN (hJQ hx))).symm

theorem typeI {G : Type} [Group G] [Finite G] {p : ℕ} {T M J₁ J₂ : Subgroup G} {z₁ : G}
    (WL : WitnessL2 p) (h : Wr p T M J₁ J₂ z₁) {A : Subgroup G} (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A) (hA1 : A ≠ ⊥)
    (hR : T ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (J₁ : Set G)) :
    ∃ K : Subgroup G, E1.IsE 1 ⊤ T A K ∧ ¬ K ≤ M := by
  rcases h.exists_not_cent hA1 with h1 | h2
  · exact typeI_aux WL h hAT hAab hR h1
  · obtain ⟨z₂, h'⟩ := h.swapW
    have hR' : T ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (J₂ : Set G) := by
      intro t ht
      have ht' : t ∈ T ⊓ Subgroup.normalizer (J₁ : Set G) := ⟨ht.1, hR ht⟩
      rw [h.normalizer_eq] at ht'
      exact ht'.2
    exact typeI_aux WL h' hAT hAab hR' h2

end CFSG.Quasithin.E2.E22N
