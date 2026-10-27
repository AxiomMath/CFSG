module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLin

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] noncomputable def ggLinConj {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') :
    (V ≃ₗ[ZMod p] V) ≃* (V' ≃ₗ[ZMod p] V') where
  toFun g := τ.symm.trans (g.trans τ)
  invFun g := τ.trans (g.trans τ.symm)
  left_inv g := by ext v; simp
  right_inv g := by ext v; simp
  map_mul' g h := by ext v; simp

private lemma ggQ2xT_apply {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V ≃ₗ[ZMod p] V) (v : V') :
    ggLinConj τ g v = τ (g (τ.symm v)) :=
  rfl

private lemma ggQ2xT_symm {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') :
    (ggLinConj τ).symm = ggLinConj τ.symm := by
  ext g
  rfl

private lemma ggQ2xT_symm_apply {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V ≃ₗ[ZMod p] V) :
    ggLinConj τ.symm (ggLinConj τ g) = g := by
  rw [← ggQ2xT_symm]
  exact (ggLinConj τ).symm_apply_apply g

private lemma ggQ2xT_apply_apply {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V ≃ₗ[ZMod p] V) (v : V) :
    ggLinConj τ g (τ v) = τ (g v) := by
  rw [ggQ2xT_apply, LinearEquiv.symm_apply_apply]

private lemma ggQ2xT_conj_reflection {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (c : V)
    (φ : Dual (ZMod p) V) (h : φ c = 2) :
    ggLinConj τ (Module.reflection h) =
      Module.reflection (show (φ.comp (τ.symm : V' ≃ₗ[ZMod p] V).toLinearMap) (τ c) = 2 by
        simp [h]) := by
  ext v
  simp [ggQ2xT_apply, Module.reflection_apply]

private lemma ggQ2xT_isReflLin_forward {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') {g : V ≃ₗ[ZMod p] V}
    (h : IsReflLin g) : IsReflLin (ggLinConj τ g) := by
  obtain ⟨c, φ, hc, rfl⟩ := h
  exact ⟨τ c, φ.comp (τ.symm : V' ≃ₗ[ZMod p] V).toLinearMap, by simp [hc],
    ggQ2xT_conj_reflection τ c φ hc⟩

private lemma ggQ2xT_isReflLin_backward {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') {g : V ≃ₗ[ZMod p] V}
    (h : IsReflLin (ggLinConj τ g)) : IsReflLin g := by
  rw [← ggQ2xT_symm_apply τ g]
  exact ggQ2xT_isReflLin_forward τ.symm h

private lemma ggQ2xT_isTransvectionLin_forward {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V')
    {g : V ≃ₗ[ZMod p] V} (h : IsTransvectionLin g) : IsTransvectionLin (ggLinConj τ g) := by
  obtain ⟨u, ψ, hu, hψ, hψu, hg⟩ := h
  refine ⟨τ u, ψ.comp (τ.symm : V' ≃ₗ[ZMod p] V).toLinearMap, ?_, ?_, ?_, fun v => ?_⟩
  · simpa using τ.injective.ne hu
  · intro h0
    apply hψ
    ext w
    obtain ⟨w', rfl⟩ := τ.symm.surjective w
    have := congrArg (fun f => f w') h0
    simpa using this
  · simp [hψu]
  · rw [ggQ2xT_apply, hg (τ.symm v)]
    simp

private lemma ggQ2xT_isTransvectionLin_backward {p : ℕ} [Fact p.Prime] {V V' : Type}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V')
    {g : V ≃ₗ[ZMod p] V} (h : IsTransvectionLin (ggLinConj τ g)) : IsTransvectionLin g := by
  rw [← ggQ2xT_symm_apply τ g]
  exact ggQ2xT_isTransvectionLin_forward τ.symm h

private lemma ggQ2xT_span_singleton_equiv {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (y z : V) :
    Submodule.span (ZMod p) {τ y} = Submodule.span (ZMod p) {τ z} ↔
      Submodule.span (ZMod p) {y} = Submodule.span (ZMod p) {z} := by
  constructor
  · intro h
    have h' := congrArg (Submodule.map (τ.symm : V' ≃ₗ[ZMod p] V).toLinearMap) h
    simpa [Submodule.map_span] using h'
  · intro h
    have h' := congrArg (Submodule.map (τ : V ≃ₗ[ZMod p] V').toLinearMap) h
    simpa [Submodule.map_span] using h'

private lemma ggQ2xT_mem_span_singleton {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (y z : V) :
    τ z ∈ Submodule.span (ZMod p) {τ y} ↔ z ∈ Submodule.span (ZMod p) {y} := by
  have hmap : (Submodule.span (ZMod p) {y}).map (τ : V ≃ₗ[ZMod p] V').toLinearMap =
      Submodule.span (ZMod p) {τ y} := by
    rw [Submodule.map_span]
    simp
  rw [← hmap, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwz⟩
    exact τ.injective hwz ▸ hw
  · rintro hz
    exact ⟨z, hz, rfl⟩

private lemma ggQ2xT_mem_normalizer {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (P : Subgroup (V ≃ₗ[ZMod p] V))
    (φ : V ≃ₗ[ZMod p] V) :
    ggLinConj τ φ ∈ Subgroup.normalizer
        ((P.map (ggLinConj τ).toMonoidHom : Subgroup (V' ≃ₗ[ZMod p] V')) :
          Set (V' ≃ₗ[ZMod p] V')) ↔
      φ ∈ Subgroup.normalizer (P : Set (V ≃ₗ[ZMod p] V)) := by
  have hmap := Subgroup.map_equiv_normalizer_eq P (ggLinConj τ)
  rw [← hmap]
  exact Subgroup.mem_map_iff_mem (ggLinConj τ).injective

theorem ggLinConj_apply {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V ≃ₗ[ZMod p] V) (v : V') :
    ggLinConj τ g v = τ (g (τ.symm v)) :=
  ggQ2xT_apply τ g v

theorem ggLinConj_isReflLin {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (g : V ≃ₗ[ZMod p] V) :
    IsReflLin (ggLinConj τ g) ↔ IsReflLin g :=
  ⟨ggQ2xT_isReflLin_backward τ, ggQ2xT_isReflLin_forward τ⟩

theorem ggLinConj_transvectionFree {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (A : Subgroup (V ≃ₗ[ZMod p] V)) :
    TransvectionFree (A.map (ggLinConj τ).toMonoidHom) ↔ TransvectionFree A := by
  constructor
  · intro h g hg hgT
    exact h (ggLinConj τ g) (Subgroup.mem_map.mpr ⟨g, hg, rfl⟩)
      (ggQ2xT_isTransvectionLin_forward τ hgT)
  · intro h g' hg' hg'T
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hg'
    exact h g hg (ggQ2xT_isTransvectionLin_backward τ hg'T)

theorem ggLinConj_reflSet {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (A : Subgroup (V ≃ₗ[ZMod p] V)) :
    {t | t ∈ A.map (ggLinConj τ).toMonoidHom ∧ IsReflLin t} =
      (ggLinConj τ) '' {t | t ∈ A ∧ IsReflLin t} := by
  ext t
  constructor
  · rintro ⟨htmap, htR⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp htmap
    exact ⟨a, ⟨ha, (ggLinConj_isReflLin τ a).mp htR⟩, rfl⟩
  · rintro ⟨a, ⟨ha, haR⟩, rfl⟩
    exact ⟨Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, (ggLinConj_isReflLin τ a).mpr haR⟩

theorem ggLinConj_reflGp {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (A : Subgroup (V ≃ₗ[ZMod p] V)) :
    reflGp (A.map (ggLinConj τ).toMonoidHom) = (reflGp A).map (ggLinConj τ).toMonoidHom := by
  rw [reflGp, reflGp, ggLinConj_reflSet]
  exact (MonoidHom.map_closure (ggLinConj τ).toMonoidHom
    {t | t ∈ A ∧ IsReflLin t}).symm

theorem ggLinConj_P3 {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (A : Subgroup (V ≃ₗ[ZMod p] V)) (x : V) :
    (∀ φ ∈ A.map (ggLinConj τ).toMonoidHom, ∃ r ∈ reflGp (A.map (ggLinConj τ).toMonoidHom),
      Submodule.span (ZMod p) {φ (τ x)} = Submodule.span (ZMod p) {r (τ x)}) ↔
    (∀ φ ∈ A, ∃ r ∈ reflGp A, Submodule.span (ZMod p) {φ x} = Submodule.span (ZMod p) {r x}) := by
  constructor
  · intro H φ hφ
    obtain ⟨r', hr', hspan'⟩ := H (ggLinConj τ φ) (Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩)
    rw [ggLinConj_reflGp] at hr'
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hr'
    refine ⟨r, hr, ?_⟩
    have h2 : Submodule.span (ZMod p) {τ (φ x)} = Submodule.span (ZMod p) {τ (r x)} := by
      simpa [ggQ2xT_apply_apply] using hspan'
    exact (ggQ2xT_span_singleton_equiv τ (φ x) (r x)).mp h2
  · intro H φ' hφ'
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hφ'
    obtain ⟨r, hr, hspan⟩ := H φ hφ
    refine ⟨ggLinConj τ r, ?_, ?_⟩
    · rw [ggLinConj_reflGp]
      exact Subgroup.mem_map.mpr ⟨r, hr, rfl⟩
    · have h2 : Submodule.span (ZMod p) {τ (φ x)} = Submodule.span (ZMod p) {τ (r x)} :=
        (ggQ2xT_span_singleton_equiv τ (φ x) (r x)).mpr hspan
      simpa [ggQ2xT_apply_apply] using h2

theorem ggLinConj_HL {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V] [Module (ZMod p) V]
    [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') (A P : Subgroup (V ≃ₗ[ZMod p] V)) (x : V) :
    (∀ φ ∈ A.map (ggLinConj τ).toMonoidHom, φ (τ x) ∈ Submodule.span (ZMod p) {τ x} →
      φ ∈ Subgroup.normalizer ((P.map (ggLinConj τ).toMonoidHom : Subgroup (V' ≃ₗ[ZMod p] V')) :
        Set (V' ≃ₗ[ZMod p] V'))) ↔
    (∀ φ ∈ A, φ x ∈ Submodule.span (ZMod p) {x} →
      φ ∈ Subgroup.normalizer (P : Set (V ≃ₗ[ZMod p] V))) := by
  constructor
  · intro H φ hφ hx
    have hx' : ggLinConj τ φ (τ x) ∈ Submodule.span (ZMod p) {τ x} := by
      rw [ggQ2xT_apply_apply]
      exact (ggQ2xT_mem_span_singleton τ x (φ x)).mpr hx
    exact (ggQ2xT_mem_normalizer τ P φ).mp
      (H (ggLinConj τ φ) (Subgroup.mem_map.mpr ⟨φ, hφ, rfl⟩) hx')
  · intro H φ' hφ' hx'
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hφ'
    have hx : φ x ∈ Submodule.span (ZMod p) {x} :=
      (ggQ2xT_mem_span_singleton τ x (φ x)).mp
        (by simpa [ggQ2xT_apply_apply] using hx')
    exact (ggQ2xT_mem_normalizer τ P φ).mpr (H φ hφ hx)

end CFSG.StandardType

end
