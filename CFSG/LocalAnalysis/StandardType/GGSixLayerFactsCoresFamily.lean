module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSLBasic

public section

namespace CFSG.StandardType

namespace LayerCores

variable {G : Type*} [Group G]

@[expose] def IsCoreFamily (H : Subgroup G) {β : Type} (S : β → Subgroup G) : Prop :=
  (∀ c, S c ≤ H) ∧ (∀ c, ∀ u ∈ H, ∀ s ∈ S c, u * s * u⁻¹ ∈ S c) ∧
    (∀ c, CFSG.IsQuasisimple (S c)) ∧ (∃ k, LayerFacts.ggDer H k ≤ ⨆ c, S c) ∧
    ∀ z ∈ ⨆ c, S c, (∀ y ∈ ⨆ c, S c, z * y = y * z) → z ^ 2 = 1 → z = 1

theorem IsCoreFamily.mono {H₀ H₁ : Subgroup G} {β : Type} {S : β → Subgroup G}
    (h : IsCoreFamily H₁ S) (h₀ : H₀ ≤ H₁) (hS : ∀ c, S c ≤ H₀) : IsCoreFamily H₀ S := by
  obtain ⟨-, hn, hq, ⟨k, hk⟩, hz⟩ := h
  exact ⟨hS, fun c u hu s hs => hn c u (h₀ hu) s hs, hq,
    ⟨k, (LayerFacts.ggDer_mono h₀ k).trans hk⟩, hz⟩

variable {G' : Type*} [Group G']

theorem IsCoreFamily.map {H : Subgroup G} {β : Type} {S : β → Subgroup G}
    (h : IsCoreFamily H S) (f : G →* G') (hf : Function.Injective f) :
    IsCoreFamily (H.map f) (fun c => (S c).map f) := by
  obtain ⟨hle, hn, hq, ⟨k, hk⟩, hz⟩ := h
  refine ⟨fun c => Subgroup.map_mono (hle c), fun c u hu s hs => ?_, fun c => ?_, ⟨k, ?_⟩,
    fun z hz' hzc hz2 => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := hu
    obtain ⟨s, hs, rfl⟩ := hs
    exact ⟨u * s * u⁻¹, hn c u hu s hs, by rw [map_mul, map_mul, map_inv]⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((S c).equivMapOfInjective f hf) (hq c)
  · rw [← LayerFacts.map_ggDer, ← Subgroup.map_iSup]
    exact Subgroup.map_mono hk
  · rw [← Subgroup.map_iSup] at hz' hzc
    obtain ⟨z, hz'', rfl⟩ := hz'
    have h1 : z = 1 := hz z hz'' (fun y hy => hf (by
      rw [map_mul, map_mul]
      exact hzc (f y) ⟨y, hy, rfl⟩)) (hf (by rw [map_pow, hz2, map_one]))
    rw [h1, map_one]

theorem IsCoreFamily.comap {H' : Subgroup G'} {β : Type} {S : β → Subgroup G'}
    (h : IsCoreFamily H' S) (f : G →* G') (hf : Function.Injective f) (hH : H' ≤ f.range) :
    IsCoreFamily (H'.comap f) (fun c => (S c).comap f) := by
  obtain ⟨hle, hn, hq, ⟨k, hk⟩, hz⟩ := h
  have hmapS : ∀ c, ((S c).comap f).map f = S c := fun c =>
    Subgroup.map_comap_eq_self ((hle c).trans hH)
  have hmapH : (H'.comap f).map f = H' := Subgroup.map_comap_eq_self hH
  refine ⟨fun c => Subgroup.comap_mono (hle c), fun c u hu s hs => ?_, fun c => ?_, ⟨k, ?_⟩,
    fun z hz' hzc hz2 => ?_⟩
  · rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hn c (f u) hu (f s) hs
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((((S c).comap f).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr (hmapS c))).symm
      (hq c)
  · rw [← Subgroup.map_le_map_iff_of_injective hf, LayerFacts.map_ggDer, hmapH,
      Subgroup.map_iSup]
    refine hk.trans (iSup_mono fun c => ?_)
    rw [hmapS c]
  · have hz'' : f z ∈ ⨆ c, S c := by
      have h1 : (⨆ c, (S c).comap f).map f = ⨆ c, S c := by
        rw [Subgroup.map_iSup]
        exact iSup_congr hmapS
      rw [← h1]
      exact Subgroup.mem_map_of_mem f hz'
    have h2 : f z = 1 := hz (f z) hz'' (fun y hy => by
      have hy' : y ∈ (⨆ c, (S c).comap f).map f := by
        rw [Subgroup.map_iSup]
        rw [iSup_congr hmapS]
        exact hy
      obtain ⟨y', hy', rfl⟩ := hy'
      rw [← map_mul, ← map_mul, hzc y' hy']) (by rw [← map_pow, hz2, map_one])
    exact hf (h2.trans (map_one f).symm)

end LayerCores

end CFSG.StandardType
