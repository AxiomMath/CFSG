module

public import CFSG.Quasithin.EmptyFaithful.SBc15Weak
public import CFSG.Quasithin.Vol2.Ch10SecKHLk2C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc15

section Quotient

variable {Γ Ŵ : Type} [Group Γ] [Group Ŵ] [Finite Ŵ]

theorem pCoreOf_map_le (ψ : Γ →* Ŵ) (hker : IsPGroup 2 ψ.ker) (J : Subgroup Γ) :
    pCoreOf 2 (J.map ψ) ≤ (pCoreOf 2 J).map ψ := by
  set Rh := pCoreOf 2 (J.map ψ) with hRh
  set R : Subgroup Γ := J ⊓ Rh.comap ψ with hR
  have hRJ : R ≤ J := inf_le_left
  have hkey : ∀ g ∈ J, ∀ y ∈ R, g * y * g⁻¹ ∈ R := by
    intro g hg y hy
    refine ⟨J.mul_mem (J.mul_mem hg hy.1) (J.inv_mem hg), ?_⟩
    have h1 : ψ g ∈ Subgroup.normalizer (Rh : Set Ŵ) :=
      le_normalizer_pCoreOf 2 (J.map ψ) (Subgroup.mem_map_of_mem ψ hg)
    have h2 := (Subgroup.mem_normalizer_iff.mp h1 (ψ y)).mp hy.2
    simpa [map_mul, map_inv] using h2
  have hRn : J ≤ Subgroup.normalizer (R : Set Γ) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hkey g hg y hy, fun hy => ?_⟩
    have := hkey g⁻¹ (J.inv_mem hg) _ hy
    simpa [mul_assoc] using this
  have hR2 : IsPGroup 2 R :=
    (IsPGroup.comap_of_ker_isPGroup (pCoreOf_isPGroup 2 (J.map ψ)) ψ hker).to_le inf_le_right
  have hRle : R ≤ pCoreOf 2 J := le_pCoreOf_of_le_normalizer 2 hRJ hRn hR2
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp (pCoreOf_le 2 _ hx)
  exact Subgroup.mem_map.mpr ⟨j, hRle ⟨hj, hx⟩, rfl⟩

theorem parabolicWeak_of_quotient (ψ : Γ →* Ŵ) (hker : IsPGroup 2 ψ.ker) {T X K : Subgroup Γ}
    (hkerT : ψ.ker ≤ T) (hXK : X ≤ K)
    (hA : ∀ g : Γ, ∃ k ∈ K.map ψ, ∃ y ∈ T.map ψ, ψ g = k * y)
    (hB : ∀ k ∈ K.map ψ,
      (∀ w ∈ pCoreOf 2 (X.map ψ ⊔ (T ⊓ K).map ψ), k * w * k⁻¹ ∈ (T ⊓ K).map ψ) →
        k ∈ X.map ψ ⊔ (T ⊓ K).map ψ) :
    ParabolicWeak T X K ⊤ := by
  refine ⟨fun g _ => ?_, fun k hk hw => ?_⟩
  · obtain ⟨kh, hkh, yh, hyh, h⟩ := hA g
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hkh
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hyh
    refine ⟨k, hk, k⁻¹ * g, ?_, by group⟩
    have hz : (k⁻¹ * g) * y⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, h]
      group
    have : k⁻¹ * g = ((k⁻¹ * g) * y⁻¹) * y := by group
    rw [this]
    exact T.mul_mem (hkerT hz) hy
  · have hJK : X ⊔ T ⊓ K ≤ K := sup_le hXK inf_le_right
    have hmem : ψ k ∈ X.map ψ ⊔ (T ⊓ K).map ψ := by
      refine hB (ψ k) (Subgroup.mem_map_of_mem ψ hk) fun wh hwh => ?_
      rw [← Subgroup.map_sup] at hwh
      obtain ⟨w, hwJ, rfl⟩ := Subgroup.mem_map.mp (pCoreOf_map_le ψ hker _ hwh)
      exact Subgroup.mem_map.mpr ⟨k * w * k⁻¹, hw w hwJ, by simp [map_mul, map_inv]⟩
    rw [← Subgroup.map_sup] at hmem
    obtain ⟨j, hj, hjk⟩ := Subgroup.mem_map.mp hmem
    have hz : j⁻¹ * k ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hjk]
      group
    have hzU : j⁻¹ * k ∈ T ⊓ K := ⟨hkerT hz, K.mul_mem (K.inv_mem (hJK hj)) hk⟩
    have : k = j * (j⁻¹ * k) := by group
    rw [this]
    exact (X ⊔ T ⊓ K).mul_mem hj (Subgroup.mem_sup_right hzU)

end Quotient

section Subtype

variable {G : Type} [Group G]

theorem parabolicWeak_of_subtype {G₁ T X K : Subgroup G} (hX : X ≤ G₁) (hT : T ≤ G₁)
    (hK : K ≤ G₁)
    (h : ParabolicWeak (T.subgroupOf G₁) (X.subgroupOf G₁) (K.subgroupOf G₁)
      (⊤ : Subgroup ↥G₁)) : ParabolicWeak T X K G₁ := by
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun g hg => ?_, fun k hk hw => ?_⟩
  · obtain ⟨k, hk, y, hy, h⟩ := hA ⟨g, hg⟩ trivial
    exact ⟨k, hk, y, hy, congrArg Subtype.val h⟩
  · have hk₁ : k ∈ G₁ := hK hk
    have hTK : T ⊓ K ≤ G₁ := inf_le_left.trans hT
    have hJ : X ⊔ T ⊓ K ≤ G₁ := sup_le hX hTK
    have hsub : (X ⊔ T ⊓ K).subgroupOf G₁ =
        X.subgroupOf G₁ ⊔ T.subgroupOf G₁ ⊓ K.subgroupOf G₁ := by
      have hinf : (T ⊓ K).subgroupOf G₁ = T.subgroupOf G₁ ⊓ K.subgroupOf G₁ :=
        Subgroup.comap_inf _ _ _
      rw [Subgroup.subgroupOf_sup hX hTK, hinf]
    have h1 := hB ⟨k, hk₁⟩ hk ?_
    · rw [← hsub] at h1
      exact h1
    · intro w hw'
      rw [← hsub] at hw'
      have hwG : (w : G) ∈ pCoreOf 2 (X ⊔ T ⊓ K) := by
        have := Subgroup.mem_map_of_mem G₁.subtype hw'
        rwa [CFSG.Quasithin.Vol2.Ch10.SecB.C10KH.pCoreOf_subgroupOf_map' hJ] at this
      have := hw _ hwG
      exact ⟨this.1, this.2⟩

end Subtype

end SBc15

end CFSG.Quasithin
