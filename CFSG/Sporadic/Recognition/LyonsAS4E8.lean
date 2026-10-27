module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47TwoGroup

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup CFSG.ComponentClassification.Foote47

theorem not_isConj_of_elementaryAbelian_eight {G : Type} [Group G] [Finite G] {x u t : G}
    (F : Subgroup G) (hF8 : Nat.card F = 8) (hF2 : ∀ f ∈ F, f ^ 2 = 1)
    (hFx : F ≤ centralizer ({x} : Set G)) (ht : orderOf t = 2) (htu : t * u = u * t)
    (hK : ¬ 8 ∣ Nat.card ↥(centralizer ({u} : Set G) ⊓ centralizer ({t} : Set G))) :
    ¬ IsConj x u := by
  rintro hconj
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  set C : Subgroup G := centralizer ({u} : Set G)
  set F' : Subgroup G := F.map (MulAut.conj g).toMonoidHom
  have hF'8 : Nat.card F' = 8 :=
    (card_map_of_injective (MulAut.conj g).injective).trans hF8
  have hF'2 : ∀ a ∈ F', a ^ 2 = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    show (g * f * g⁻¹) ^ 2 = 1
    rw [conj_pow, hF2 f hf]
    simp
  have hF'C : F' ≤ C := by
    rintro _ ⟨f, hf, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hfx : f * x = x * f := mem_centralizer_singleton_iff.1 (hFx hf)
    rw [← hg]
    show g * f * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * f * g⁻¹)
    calc g * f * g⁻¹ * (g * x * g⁻¹) = g * (f * x) * g⁻¹ := by group
      _ = g * (x * f) * g⁻¹ := by rw [hfx]
      _ = g * x * g⁻¹ * (g * f * g⁻¹) := by group
  have htC : t ∈ C := mem_centralizer_singleton_iff.2 htu
  let tC : C := ⟨t, htC⟩
  have hF₀ : IsPGroup 2 (F'.subgroupOf C) :=
    IsPGroup.of_card (n := 3) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hF'C).toEquiv, hF'8]
      norm_num)
  have htC2 : orderOf tC = 2 := by
    rw [← ht]
    exact (orderOf_injective C.subtype C.subtype_injective tC).symm
  have hZ₀ : IsPGroup 2 (zpowers tC) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htC2]; norm_num)
  obtain ⟨Q₁, hQ₁⟩ := hF₀.exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := hZ₀.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q₁ Q₂
  have hconjQ : ∀ a ∈ (Q₁ : Subgroup C), c * a * c⁻¹ ∈ (Q₂ : Subgroup C) := by
    intro a ha
    rw [← hc]
    exact smul_mem_pointwise_smul a (MulAut.conj c) (Q₁ : Subgroup C) ha
  set T : Subgroup G := (Q₂ : Subgroup C).map C.subtype
  set F₁ : Subgroup G := F'.map (MulAut.conj (c : G)).toMonoidHom
  have hT : IsPGroup 2 T := Q₂.isPGroup'.map C.subtype
  have htT : t ∈ T := ⟨tC, hQ₂ (mem_zpowers tC), rfl⟩
  have hF₁T : F₁ ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨c * ⟨a, hF'C ha⟩ * c⁻¹, hconjQ _ (hQ₁ (mem_subgroupOf.2 ha)), rfl⟩
  have hF₁8 : Nat.card F₁ = 8 :=
    (card_map_of_injective (MulAut.conj (c : G)).injective).trans hF'8
  have hF₁2 : ∀ a ∈ F₁, a ^ 2 = 1 := by
    rintro _ ⟨f, hf, rfl⟩
    show ((c : G) * f * (c : G)⁻¹) ^ 2 = 1
    rw [conj_pow, hF'2 f hf]
    simp
  have h8 := eight_le_card_inf_centralizer hT hF₁T hF₁2 hF₁8 htT ht
  have hle : T ⊓ centralizer ({t} : Set G) ≤ C ⊓ centralizer ({t} : Set G) :=
    inf_le_inf_right _ (map_subtype_le _)
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (hT.to_inf_left : IsPGroup 2 ↥(T ⊓ centralizer {t}))
  have hj3 : 3 ≤ j := by
    by_contra hlt
    have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h8d : 8 ∣ Nat.card ↥(T ⊓ centralizer ({t} : Set G)) := by
    rw [hj]
    simpa using (pow_dvd_pow 2 hj3 : 2 ^ 3 ∣ 2 ^ j)
  exact hK (h8d.trans (card_dvd_of_le hle))

end CFSG.Sporadic.Recognition.LyonsSims
