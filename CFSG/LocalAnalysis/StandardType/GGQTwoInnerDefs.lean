module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSchur
public import CFSG.LocalAnalysis.StandardType.GGQTwoCoreDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] def GGQ2QuandleInner {H : Type} [Group H] (T Γ : Set H) : Prop :=
  ∀ π : H → H, (∀ t ∈ T, π t ∈ T) → Set.InjOn π T →
    (∀ s ∈ T, ∀ t ∈ T, π (s * t * s⁻¹) = π s * π t * (π s)⁻¹) →
      ∃ g ∈ Γ, ∀ t ∈ T, π t = g * t * g⁻¹

@[expose] def ggReflSet {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)) : Set (V ≃ₗ[ZMod p] V) :=
  {t | t ∈ A ∧ IsReflLin t}

theorem ggQ2_isReflLin_conj {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (a t : V ≃ₗ[ZMod p] V) (ht : IsReflLin t) : IsReflLin (a * t * a⁻¹) := by
  obtain ⟨c, φ, h, rfl⟩ := ht
  refine ⟨a c, φ.comp (a⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap, ?_, ?_⟩
  · simpa using h
  · ext v
    simp [Module.reflection_apply]

theorem ggQ2_inner_map {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {T Γ : Set H}
    (h : GGQ2QuandleInner T Γ) : GGQ2QuandleInner (e '' T) (e '' Γ) := by
  intro π' hT hinj hπ
  obtain ⟨g, hg, hgt⟩ := h (fun t => e.symm (π' (e t)))
    (by
      intro t ht
      obtain ⟨u, hu, hue⟩ := hT (e t) ⟨t, ht, rfl⟩
      rw [← hue]
      simpa using hu)
    (by
      intro s hs t ht hst
      have h1 : π' (e s) = π' (e t) := by simpa using congrArg e hst
      exact e.injective (hinj ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ h1))
    (by
      intro s hs t ht
      have := hπ (e s) ⟨s, hs, rfl⟩ (e t) ⟨t, ht, rfl⟩
      simp only [map_mul, map_inv]
      rw [this]
      simp only [map_mul, map_inv])
  refine ⟨e g, ⟨g, hg, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have := congrArg e (hgt t ht)
  simpa using this

theorem ggQ2_inner_of_hom {H H' : Type} [Group H] [Group H'] (f : H →* H')
    (hf : Function.Injective f) {T Γ : Set H} {Γ' : Set H'}
    (hTc : ∀ s ∈ T, ∀ t ∈ T, s * t * s⁻¹ ∈ T)
    (h : GGQ2QuandleInner (f '' T) Γ') (hΓ : Γ' ⊆ f '' Γ) : GGQ2QuandleInner T Γ := by
  classical
  intro π hT hinj hπ
  let π' : H' → H' := fun y =>
    if hy : ∃ t ∈ T, f t = y then f (π (Classical.choose hy)) else y
  have hπ'f : ∀ t ∈ T, π' (f t) = f (π t) := by
    intro t ht
    have hy : ∃ t' ∈ T, f t' = f t := ⟨t, ht, rfl⟩
    have hc := Classical.choose_spec hy
    have hct : Classical.choose hy = t := hf hc.2
    simp only [π', dif_pos hy, hct]
  obtain ⟨g', hg', hg't⟩ := h π'
    (by
      rintro _ ⟨t, ht, rfl⟩
      rw [hπ'f t ht]
      exact ⟨π t, hT t ht, rfl⟩)
    (by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hst
      rw [hπ'f s hs, hπ'f t ht] at hst
      exact congrArg f (hinj hs ht (hf hst)))
    (by
      rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
      have h1 : f s * f t * (f s)⁻¹ = f (s * t * s⁻¹) := by simp
      rw [h1, hπ'f _ (hTc s hs t ht), hπ s hs t ht, hπ'f s hs, hπ'f t ht]
      simp)
  obtain ⟨g, hg, rfl⟩ := hΓ hg'
  refine ⟨g, hg, fun t ht => hf ?_⟩
  have := hg't (f t) ⟨t, ht, rfl⟩
  rw [hπ'f t ht] at this
  simpa using this

theorem ggQ2_transfer {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p) (hbas : D.Basis)
    (h4 : 4 ≤ Fintype.card D.ι) (A : Subgroup (D.V ≃ₗ[ZMod p] D.V)) (hW : D.weyl ≤ A)
    (Γ : Set (D.V ≃ₗ[ZMod p] D.V)) (hΓ : GGQ2QuandleInner (ggReflSet A) Γ) :
    ∀ a ∈ A, ∃ g ∈ Γ, (∀ v, a v = g v) ∨ (∀ v, a v = -(g v)) := by
  intro a ha
  obtain ⟨g, hg, hgt⟩ := hΓ (fun t => a * t * a⁻¹)
    (by
      rintro t ⟨htA, htR⟩
      exact ⟨A.mul_mem (A.mul_mem ha htA) (A.inv_mem ha), ggQ2_isReflLin_conj a t htR⟩)
    (by
      intro s _ t _ hst
      simpa using hst)
    (by
      intro s _ t _
      simp [mul_assoc])
  refine ⟨g, hg, ggQ2_lemmaN hp D hbas h4 a g ?_⟩
  intro k
  have hk : D.simpleRefl k ∈ ggReflSet A :=
    ⟨hW (Subgroup.subset_closure ⟨k, Set.mem_univ k, rfl⟩),
      ⟨D.coroot k, D.root k, D.root_coroot_self k, rfl⟩⟩
  exact hgt (D.simpleRefl k) hk

theorem ggQ2_P3_of_pm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)) (x : V)
    (h : ∀ a ∈ A, ∃ r ∈ reflGp A, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v))) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod p) {φ x} = Submodule.span (ZMod p) {r x} := by
  intro φ hφ
  obtain ⟨r, hr, hpm⟩ := h φ hφ
  refine ⟨r, hr, ?_⟩
  rcases hpm with h1 | h1
  · rw [h1 x]
  · rw [h1 x, Submodule.span_singleton_eq_span_singleton]
    exact ⟨-1, by simp⟩

@[expose] noncomputable def ggBCReflGp {m : ℕ} (S : Set (GGBCV m)) :
    Subgroup (GGBCV m ≃ₗ[ZMod 3] GGBCV m) :=
  Subgroup.closure (ggBCReflSet S)

@[expose] def ggDHalfSpin {m : ℕ} (ε : ZMod 3) (z : GGBCV m) : Prop :=
  (∀ i, z i ≠ 0) ∧ ∏ i, z i = ε

theorem ggQ2_inner_image {H H' : Type} [Group H] [Group H'] (f : H →* H')
    (hf : Function.Injective f) {T Γ : Set H}
    (hTc : ∀ s ∈ T, ∀ t ∈ T, s * t * s⁻¹ ∈ T)
    (h : GGQ2QuandleInner T Γ) : GGQ2QuandleInner (f '' T) (f '' Γ) := by
  classical
  intro π' hT' hinj' hπ'
  have hex : ∀ t ∈ T, ∃ u ∈ T, f u = π' (f t) := by
    intro t ht
    obtain ⟨u, hu, hue⟩ := hT' (f t) ⟨t, ht, rfl⟩
    exact ⟨u, hu, hue⟩
  let π : H → H := fun t => if ht : ∃ u ∈ T, f u = π' (f t) then Classical.choose ht else t
  have hπf : ∀ t ∈ T, f (π t) = π' (f t) := by
    intro t ht
    simp only [π, dif_pos (hex t ht)]
    exact (Classical.choose_spec (hex t ht)).2
  have hπT : ∀ t ∈ T, π t ∈ T := by
    intro t ht
    simp only [π, dif_pos (hex t ht)]
    exact (Classical.choose_spec (hex t ht)).1
  obtain ⟨g, hg, hgt⟩ := h π hπT
    (by
      intro s hs t ht hst
      have h1 : π' (f s) = π' (f t) := by rw [← hπf s hs, ← hπf t ht, hst]
      exact hf (hinj' ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ h1))
    (by
      intro s hs t ht
      apply hf
      have h1 : f s * f t * (f s)⁻¹ = f (s * t * s⁻¹) := by simp
      rw [hπf _ (hTc s hs t ht), ← h1, hπ' (f s) ⟨s, hs, rfl⟩ (f t) ⟨t, ht, rfl⟩,
        ← hπf s hs, ← hπf t ht]
      simp)
  refine ⟨f g, ⟨g, hg, rfl⟩, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  rw [← hπf t ht, hgt t ht]
  simp

end CFSG.StandardType

end
