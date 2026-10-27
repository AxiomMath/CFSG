module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.FieldTheory.Finiteness

public section

namespace CFSG.RankThree.GF2n.Smith81

open Module

section Helpers

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

private theorem alt_neg_aux (B : LinearMap.BilinForm K E) (halt : ∀ e, B e e = 0) (e f : E) :
    B e f = - B f e := by
  have h := halt (e + f)
  simp only [map_add, LinearMap.add_apply, halt e, halt f, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

private theorem eq_zero_of_mem_right (B : LinearMap.BilinForm K E)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (W₁ W₂ : Submodule K E) (hsup : W₁ ⊔ W₂ = ⊤)
    (hW₂ : ∀ u ∈ W₂, ∀ v ∈ W₂, B u v = 0) {u : E} (hu : u ∈ W₂)
    (h : ∀ v ∈ W₁, B u v = 0) : u = 0 := by
  apply hnd u
  intro f
  have hf : f ∈ W₁ ⊔ W₂ := by rw [hsup]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
  rw [map_add, h y hy, hW₂ u hu z hz, add_zero]

private theorem eq_zero_of_mem_left (B : LinearMap.BilinForm K E)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (W₁ W₂ : Submodule K E) (hsup : W₁ ⊔ W₂ = ⊤)
    (hW₁ : ∀ u ∈ W₁, ∀ v ∈ W₁, B u v = 0) {u : E} (hu : u ∈ W₁)
    (h : ∀ v ∈ W₂, B u v = 0) : u = 0 :=
  eq_zero_of_mem_right B hnd W₂ W₁ (by rwa [sup_comm]) hW₁ hu h

private theorem exists_preimage_of_mapsTo [FiniteDimensional K E] (g : E ≃ₗ[K] E)
    (W : Submodule K E) (hg : ∀ u ∈ W, g u ∈ W) {u : E} (hu : u ∈ W) :
    ∃ x ∈ W, g x = u := by
  let f : W →ₗ[K] W := (g : E →ₗ[K] E).restrict hg
  have hinj : Function.Injective f := by
    intro x y hxy
    have : g x = g y := congrArg Subtype.val hxy
    exact Subtype.ext (g.injective this)
  obtain ⟨x, hx⟩ := LinearMap.injective_iff_surjective.1 hinj ⟨u, hu⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

private theorem symm_mem_of_mapsTo [FiniteDimensional K E] (g : E ≃ₗ[K] E)
    (W : Submodule K E) (hg : ∀ u ∈ W, g u ∈ W) {u : E} (hu : u ∈ W) : g.symm u ∈ W := by
  obtain ⟨x, hx, rfl⟩ := exists_preimage_of_mapsTo g W hg hu
  simpa using hx

end Helpers

theorem exists_sub_of_orth_fixed {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (halt : ∀ e, B e e = 0)
    (T : E ≃ₗ[K] E) (hT : ∀ u v, B (T u) (T v) = B u v) {v : E}
    (hv : ∀ k, T k = k → B v k = 0) : ∃ u, v = T u - u := by
  have hrefl : B.IsRefl := fun x y h => by rw [alt_neg_aux B halt, h, neg_zero]
  have hsep : ∀ y, (∀ x, B x y = 0) → y = 0 := fun y hy =>
    hnd y fun f => by rw [alt_neg_aux B halt, hy f, neg_zero]
  have hB : B.Nondegenerate := ⟨hnd, hsep⟩
  let S : Submodule K E := LinearMap.range ((T : E →ₗ[K] E) - LinearMap.id)
  have key : ∀ w ∈ B.orthogonal S, T w = w := by
    intro w hw
    have h0 : ∀ u, B u (T.symm w - w) = 0 := by
      intro u
      have h1 := hw (T u - u) ⟨u, by simp⟩
      have h2 : B (T u) w = B u (T.symm w) := by
        have := hT u (T.symm w)
        rwa [LinearEquiv.apply_symm_apply] at this
      rw [map_sub, LinearMap.sub_apply, h2] at h1
      rw [map_sub]
      exact h1
    have h4 : T.symm w = w := sub_eq_zero.1 (hsep _ h0)
    exact (T.symm_apply_eq.1 h4).symm
  have hvS : v ∈ B.orthogonal (B.orthogonal S) := by
    intro k hk
    exact hrefl _ _ (hv k (key k hk))
  rw [LinearMap.BilinForm.orthogonal_orthogonal hB hrefl S] at hvS
  obtain ⟨u, hu⟩ := hvS
  exact ⟨u, by simpa using hu.symm⟩

section Counting

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

private theorem exists_dual_of_transv (W : Submodule K E) {c : E} (hc : c ∈ W) (hc0 : c ≠ 0)
    (g : E →ₗ[K] E) (hg : ∀ u ∈ W, ∃ s : K, g u - u = s • c) (hgc : g c = c) :
    ∃ φ ∈ (Submodule.span K {(⟨c, hc⟩ : W)}).dualAnnihilator, ∀ u : W, g u - u = φ u • c := by
  choose s hs using fun u : W => hg u u.2
  have hinj := smul_left_injective K hc0
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K W, ∀ u : W, g u - u = φ u • c := by
    refine ⟨{ toFun := s, map_add' := ?_, map_smul' := ?_ }, hs⟩
    · intro x y
      apply hinj
      simp only [add_smul]
      rw [← hs x, ← hs y, ← hs (x + y)]
      simp only [Submodule.coe_add, map_add]
      abel
    · intro r x
      apply hinj
      simp only [RingHom.id_apply, smul_eq_mul, mul_smul]
      rw [← hs x, ← hs (r • x)]
      simp only [Submodule.coe_smul, map_smul, smul_sub]
  refine ⟨φ, ?_, hφ⟩
  rw [Submodule.mem_dualAnnihilator]
  intro w hw
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
  have h0 : φ ⟨c, hc⟩ = 0 := by
    have h1 := hφ ⟨c, hc⟩
    simp only [hgc, sub_self] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_right hc0
  rw [map_smul, h0, smul_zero]

private theorem card_mul_le_of_inj {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Finite K] {α : Type*} (D : Submodule K (Module.Dual K V))
    (hD : finrank K D + 1 = finrank K V) (F : α → D) (inj : Function.Injective F) :
    Nat.card α * Nat.card K ≤ Nat.card V := by
  have : Finite D := Module.finite_of_finite K
  have h1 : Nat.card α ≤ Nat.card D := Nat.card_le_card_of_injective F inj
  have h2 : Nat.card D = Nat.card K ^ finrank K D :=
    Module.natCard_eq_pow_finrank (K := K) (V := D)
  have h3 : Nat.card V = Nat.card K ^ finrank K V :=
    Module.natCard_eq_pow_finrank (K := K) (V := V)
  calc Nat.card α * Nat.card K ≤ Nat.card D * Nat.card K := Nat.mul_le_mul_right _ h1
    _ = Nat.card K ^ finrank K D * Nat.card K := by rw [h2]
    _ = Nat.card K ^ (finrank K D + 1) := (pow_succ _ _).symm
    _ = Nat.card V := by rw [hD, h3]

end Counting

set_option linter.unusedVariables false in
theorem la_card_le {K E : Type*} [Field K] [Finite K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (halt : ∀ e, B e e = 0)
    (W₁ W₂ : Submodule K E) (hsup : W₁ ⊔ W₂ = ⊤) (hint : W₁ ⊓ W₂ = ⊥)
    (hW₁ : ∀ u ∈ W₁, ∀ v ∈ W₁, B u v = 0) (hW₂ : ∀ u ∈ W₂, ∀ v ∈ W₂, B u v = 0)
    {c : E} (hc : c ∈ W₁) (hc0 : c ≠ 0) (Γ : Subgroup (E ≃ₗ[K] E))
    (hΓ : ∀ g ∈ Γ, (∀ u ∈ W₁, g u ∈ W₁) ∧ (∀ u ∈ W₂, g u ∈ W₂) ∧
      (∀ u v, B (g u) (g v) = B u v) ∧ g c = c ∧ ∀ u ∈ W₁, ∃ s : K, g u - u = s • c) :
    Nat.card Γ * Nat.card K ≤ Nat.card W₁ := by
  have hc0' : (⟨c, hc⟩ : W₁) ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  choose F hFD hF using fun g : Γ =>
    exists_dual_of_transv W₁ hc hc0 (g.1 : E →ₗ[K] E) (hΓ g.1 g.2).2.2.2.2 (hΓ g.1 g.2).2.2.2.1
  have inj : Function.Injective fun g : Γ => (⟨F g, hFD g⟩ :
      (Submodule.span K {(⟨c, hc⟩ : W₁)}).dualAnnihilator) := by
    intro g g' hgg
    have hF1 : F g = F g' := congrArg Subtype.val hgg
    have hW1 : ∀ u ∈ W₁, g.1 u = g'.1 u := by
      intro u hu
      have h1 := hF g ⟨u, hu⟩
      have h2 := hF g' ⟨u, hu⟩
      rw [hF1] at h1
      exact sub_left_injective (h1.trans h2.symm)
    have hW2 : ∀ u ∈ W₂, g.1 u = g'.1 u := by
      intro u hu
      have hdiff : g.1 u - g'.1 u ∈ W₂ :=
        W₂.sub_mem ((hΓ g.1 g.2).2.1 u hu) ((hΓ g'.1 g'.2).2.1 u hu)
      apply sub_eq_zero.1
      apply eq_zero_of_mem_right B hnd W₁ W₂ hsup hW₂ hdiff
      intro v hv
      obtain ⟨x, hx, rfl⟩ := exists_preimage_of_mapsTo g.1 W₁ (hΓ g.1 g.2).1 hv
      rw [map_sub, LinearMap.sub_apply, (hΓ g.1 g.2).2.2.1 u x, hW1 x hx,
        (hΓ g'.1 g'.2).2.2.1 u x, sub_self]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro e
    have he : e ∈ W₁ ⊔ W₂ := by rw [hsup]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 he
    rw [map_add, map_add, hW1 y hy, hW2 z hz]
  refine card_mul_le_of_inj _ ?_ _ inj
  have := Subspace.finrank_add_finrank_dualAnnihilator_eq (Submodule.span K {(⟨c, hc⟩ : W₁)})
  rw [finrank_span_singleton hc0'] at this
  omega

section Dichotomy

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

private theorem exists_orth_witness (B : LinearMap.BilinForm K E)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (W₁ W₂ : Submodule K E) (hsup : W₁ ⊔ W₂ = ⊤)
    (hW₁ : ∀ u ∈ W₁, ∀ v ∈ W₁, B u v = 0) {c w : E} (hc : c ∈ W₁) (hw : w ∈ W₁)
    (hc0 : c ≠ 0) (hwc : ∀ a : K, w ≠ a • c) :
    ∃ φ ∈ W₂, B c φ = 0 ∧ B w φ ≠ 0 := by
  have hex : ∀ x ∈ W₁, x ≠ 0 → ∃ φ ∈ W₂, B x φ ≠ 0 := by
    intro x hx hx0
    by_contra hcon
    push Not at hcon
    exact hx0 (eq_zero_of_mem_left B hnd W₁ W₂ hsup hW₁ hx hcon)
  obtain ⟨φ₁, hφ₁, hcφ₁⟩ := hex c hc hc0
  obtain ⟨a, ha⟩ : ∃ a : K, a = B w φ₁ / B c φ₁ := ⟨_, rfl⟩
  have hx : w - a • c ∈ W₁ := W₁.sub_mem hw (W₁.smul_mem a hc)
  have hx0 : w - a • c ≠ 0 := fun h => hwc a (sub_eq_zero.1 h)
  have hxφ₁ : B (w - a • c) φ₁ = 0 := by
    simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, ha]
    field_simp
    ring
  obtain ⟨φ₂, hφ₂, hxφ₂⟩ := hex _ hx hx0
  obtain ⟨r, hr⟩ : ∃ r : K, r = B c φ₂ / B c φ₁ := ⟨_, rfl⟩
  refine ⟨φ₂ - r • φ₁, W₂.sub_mem hφ₂ (W₂.smul_mem _ hφ₁), ?_, ?_⟩
  · simp only [map_sub, map_smul, smul_eq_mul, hr]
    field_simp
    ring
  · have h1 : B c (φ₂ - r • φ₁) = 0 := by
      simp only [map_sub, map_smul, smul_eq_mul, hr]
      field_simp
      ring
    have h2 : B (w - a • c) (φ₂ - r • φ₁) = B (w - a • c) φ₂ := by
      rw [map_sub, map_smul, hxφ₁, smul_zero, sub_zero]
    have h3 : B w (φ₂ - r • φ₁) = B (w - a • c) (φ₂ - r • φ₁) := by
      have : B w (φ₂ - r • φ₁) =
          B (w - a • c) (φ₂ - r • φ₁) + a * B c (φ₂ - r • φ₁) := by
        simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring
      rw [this, h1, mul_zero, add_zero]
    rw [h3, h2]
    exact hxφ₂

end Dichotomy

set_option linter.unusedVariables false in
theorem la_dichotomy {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hnd : ∀ e, (∀ f, B e f = 0) → e = 0) (halt : ∀ e, B e e = 0)
    (W₁ W₂ : Submodule K E) (hsup : W₁ ⊔ W₂ = ⊤) (hint : W₁ ⊓ W₂ = ⊥)
    (hW₁ : ∀ u ∈ W₁, ∀ v ∈ W₁, B u v = 0) (hW₂ : ∀ u ∈ W₂, ∀ v ∈ W₂, B u v = 0)
    (T g : E ≃ₗ[K] E) (hT : ∀ u v, B (T u) (T v) = B u v)
    (hg : ∀ u v, B (g u) (g v) = B u v) (hTT : ∀ u, T (T u) = u)
    (hT₁ : ∀ u ∈ W₁, T u ∈ W₁) (hT₂ : ∀ u ∈ W₂, T u ∈ W₂)
    (hg₁ : ∀ u ∈ W₁, g u ∈ W₁) (hg₂ : ∀ u ∈ W₂, g u ∈ W₂)
    {c β : E} (hc : c ∈ W₁) (hβ : β ∈ W₂) (hc0 : c ≠ 0) (hβ0 : β ≠ 0)
    (hN₁ : ∀ u ∈ W₁, ∃ s : K, T u - u = s • c) (hN₂ : ∀ u ∈ W₂, ∃ s : K, T u - u = s • β)
    (hu₁ : ∃ u ∈ W₁, T u - u = c) (hu₂ : ∃ u ∈ W₂, T u - u = β)
    (hgc : g c = c) (Dt : AddSubgroup E)
    (hDt : ∀ e ∈ Dt, ∃ s t : K, e = s • c + t • β)
    (hgD : ∀ v, T v = v → g v - v ∈ Dt) :
    (∀ u ∈ W₁, ∃ s : K, g u - u = s • c) ∨ (∀ t : K, t • β ∈ Dt) := by
  have hneg := alt_neg_aux B halt
  have hsa : ∀ x y, B (T x - x) y = B x (T y - y) := by
    intro x y
    have h := hT x (T y)
    rw [hTT y] at h
    simp only [map_sub, LinearMap.sub_apply]
    rw [h]
  by_cases hleft : ∀ u ∈ W₁, ∃ s : K, g u - u = s • c
  · exact Or.inl hleft
  right
  push Not at hleft
  obtain ⟨u₀, hu₀, hu₀ne⟩ := hleft
  obtain ⟨u₁, hu₁W, hu₁c⟩ := hu₁
  obtain ⟨u₂, hu₂W, hu₂β⟩ := hu₂
  have hβpair : ∀ v, B β v = B u₂ (T v - v) := fun v => by rw [← hu₂β, hsa]
  have hu₂c : B u₂ c ≠ 0 := by
    intro h0
    apply hβ0
    apply eq_zero_of_mem_right B hnd W₁ W₂ hsup hW₂ hβ
    intro v hv
    obtain ⟨s, hs⟩ := hN₁ v hv
    rw [hβpair, hs, map_smul, h0, smul_zero]
  have hβu₁ : B β u₁ ≠ 0 := by
    rw [hβpair, hu₁c]
    exact hu₂c
  have hE : ∀ φ ∈ W₂, B c φ = 0 → T φ = φ := by
    intro φ hφ hcφ
    obtain ⟨t, ht⟩ := hN₂ φ hφ
    have h1 : B (T φ - φ) u₁ = 0 := by
      rw [hsa, hu₁c, hneg φ c, hcφ, neg_zero]
    rw [ht, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    have h2 : t = 0 := (mul_eq_zero.1 h1).resolve_right hβu₁
    rw [h2, zero_smul] at ht
    exact sub_eq_zero.1 ht
  have hA : ∀ v ∈ W₁, T v = v → ∃ s : K, g v - v = s • c := by
    intro v hv hTv
    obtain ⟨s, t, hst⟩ := hDt _ (hgD v hTv)
    have hmem : t • β ∈ W₁ ⊓ W₂ := by
      refine ⟨?_, W₂.smul_mem t hβ⟩
      have h : t • β = (g v - v) - s • c := by rw [hst]; abel
      rw [h]
      exact W₁.sub_mem (W₁.sub_mem (hg₁ v hv) hv) (W₁.smul_mem s hc)
    rw [hint, Submodule.mem_bot] at hmem
    have ht : t = 0 := (smul_eq_zero.1 hmem).resolve_right hβ0
    exact ⟨s, by rw [hst, ht, zero_smul, add_zero]⟩
  have hB : ∀ s : K, g u₁ - u₁ ≠ s • c := by
    intro s'' hs''
    obtain ⟨s, hs⟩ := hN₁ u₀ hu₀
    have hfW : u₀ - s • u₁ ∈ W₁ := W₁.sub_mem hu₀ (W₁.smul_mem s hu₁W)
    have hfT : T (u₀ - s • u₁) = u₀ - s • u₁ := by
      have h0 : T (u₀ - s • u₁) - (u₀ - s • u₁) = 0 := by
        have e : T (u₀ - s • u₁) - (u₀ - s • u₁) = (T u₀ - u₀) - s • (T u₁ - u₁) := by
          simp only [map_sub, map_smul]
          module
        rw [e, hs, hu₁c, sub_self]
      exact sub_eq_zero.1 h0
    obtain ⟨s', hs'⟩ := hA _ hfW hfT
    apply hu₀ne (s' + s * s'')
    have e : g u₀ - u₀ = (g (u₀ - s • u₁) - (u₀ - s • u₁)) + s • (g u₁ - u₁) := by
      simp only [map_sub, map_smul]
      module
    rw [e, hs', hs'', add_smul, mul_smul]
  have hw'W : g.symm u₁ - u₁ ∈ W₁ := W₁.sub_mem (symm_mem_of_mapsTo g W₁ hg₁ hu₁W) hu₁W
  have hw'c : ∀ a : K, g.symm u₁ - u₁ ≠ a • c := by
    intro a ha
    apply hB (-a)
    have h1 : g.symm u₁ = a • c + u₁ := eq_add_of_sub_eq ha
    have h2 : u₁ = a • c + g u₁ := by
      have := congrArg g h1
      rwa [LinearEquiv.apply_symm_apply, map_add, map_smul, hgc] at this
    calc g u₁ - u₁ = g u₁ - (a • c + g u₁) := by rw [← h2]
      _ = (-a) • c := by rw [neg_smul]; abel
  obtain ⟨φ₀, hφ₀W, hcφ₀, hw'φ₀⟩ := exists_orth_witness B hnd W₁ W₂ hsup hW₁ hc hw'W hc0 hw'c
  have hTφ₀ : T φ₀ = φ₀ := hE φ₀ hφ₀W hcφ₀
  obtain ⟨s, t, hst⟩ := hDt _ (hgD φ₀ hTφ₀)
  have hs0 : s = 0 := by
    have hmem : s • c ∈ W₁ ⊓ W₂ := by
      refine ⟨W₁.smul_mem s hc, ?_⟩
      have h : s • c = (g φ₀ - φ₀) - t • β := by rw [hst]; abel
      rw [h]
      exact W₂.sub_mem (W₂.sub_mem (hg₂ φ₀ hφ₀W) hφ₀W) (W₂.smul_mem t hβ)
    rw [hint, Submodule.mem_bot] at hmem
    exact (smul_eq_zero.1 hmem).resolve_right hc0
  have hgφ₀ : g φ₀ - φ₀ = t • β := by rw [hst, hs0, zero_smul, zero_add]
  have ht : t ≠ 0 := by
    intro ht0
    apply hw'φ₀
    have h1 : B (g φ₀ - φ₀) u₁ = B φ₀ (g.symm u₁ - u₁) := by
      have h := hg φ₀ (g.symm u₁)
      rw [LinearEquiv.apply_symm_apply] at h
      simp only [map_sub, LinearMap.sub_apply]
      rw [h]
    rw [hgφ₀, ht0, zero_smul, map_zero, LinearMap.zero_apply] at h1
    rw [hneg _ φ₀, ← h1, neg_zero]
  intro r
  have hφ : (r * t⁻¹) • φ₀ ∈ W₂ := W₂.smul_mem _ hφ₀W
  have hc' : B c ((r * t⁻¹) • φ₀) = 0 := by rw [map_smul, hcφ₀, smul_zero]
  have h := hgD _ (hE _ hφ hc')
  have e : g ((r * t⁻¹) • φ₀) - (r * t⁻¹) • φ₀ = r • β := by
    rw [map_smul, ← smul_sub, hgφ₀, smul_smul, mul_assoc, inv_mul_cancel₀ ht, mul_one]
  rwa [e] at h

end CFSG.RankThree.GF2n.Smith81
