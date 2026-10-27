module

public import Mathlib.Basic.Finite.Prod
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Coset.Defs

public section

namespace CFSG.Quasithin.SimsD1.Embed

private def actOf {Ω A X : Type} [Group A] (ψ : Ω ≃ A × X) : A →* Equiv.Perm Ω where
  toFun g := ψ.trans ((Equiv.prodCongr (Equiv.mulRight g⁻¹) (Equiv.refl X)).trans ψ.symm)
  map_one' := by
    ext ω
    simp
  map_mul' g h := by
    ext ω
    simp [mul_assoc, Prod.ext_iff]

private theorem actOf_apply {Ω A X : Type} [Group A] (ψ : Ω ≃ A × X) (g : A) (ω : Ω) :
    actOf ψ g ω = ψ.symm ((ψ ω).1 * g⁻¹, (ψ ω).2) := rfl

private theorem actOf_apply_eq_iff {Ω A X : Type} [Group A] (ψ : Ω ≃ A × X) (g : A)
    (ω ω' : Ω) : actOf ψ g ω = ω' ↔ ψ ω' = ((ψ ω).1 * g⁻¹, (ψ ω).2) := by
  rw [actOf_apply, Equiv.symm_apply_eq]
  exact eq_comm

private theorem actOf_injective {Ω A X : Type} [Group A] [Nonempty X] (ψ : Ω ≃ A × X) :
    Function.Injective (actOf ψ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨x⟩ := ‹Nonempty X›
  have h := (actOf_apply_eq_iff ψ g (ψ.symm (1, x)) (ψ.symm (1, x))).1 (by rw [hg]; rfl)
  simpa using h.symm

theorem exists_transversal_equiv {A T : Type} [Group A] [Group T] (j : T →* A)
    (hj : Function.Injective j) :
    ∃ (Q : Type) (φ : Q × T ≃ A), ∀ (c : Q) (s s' : T), φ (c, s * s') = φ (c, s) * j s' := by
  obtain ⟨r, hr⟩ := (QuotientGroup.mk_surjective (s := j.range)).hasRightInverse
  have hmk : ∀ (c : A ⧸ j.range) (s : T), (↑(r c * j s) : A ⧸ j.range) = c := fun c s => by
    rw [QuotientGroup.mk_mul_of_mem _ (MonoidHom.mem_range.2 ⟨s, rfl⟩), hr c]
  have hbij : Function.Bijective (fun p : (A ⧸ j.range) × T => r p.1 * j p.2) := by
    refine ⟨fun ⟨c, s⟩ ⟨c', s'⟩ h => ?_, fun x => ?_⟩
    · obtain rfl : c = c' :=
        (hmk c s).symm.trans ((congrArg QuotientGroup.mk h).trans (hmk c' s'))
      exact Prod.ext rfl (hj (mul_left_cancel h))
    · obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 (QuotientGroup.eq.1 (hr (x : A ⧸ j.range)))
      exact ⟨(x, s), by simp only [hs, mul_inv_cancel_left]⟩
  exact ⟨A ⧸ j.range, Equiv.ofBijective _ hbij, fun c s s' => by simp [mul_assoc]⟩

private def psiL {A T Q X : Type} (φ : Q × T ≃ A) : T × Q × X ≃ A × X where
  toFun ω := (φ (ω.2.1, ω.1), ω.2.2)
  invFun y := ((φ.symm y.1).2, (φ.symm y.1).1, y.2)
  left_inv := fun ⟨s, c, x⟩ => by simp
  right_inv := fun ⟨a, x⟩ => by simp

private def psiR {A T Q X : Type} (φ : Q × T ≃ A) : T × X × Q ≃ A × X where
  toFun ω := (φ (ω.2.2, ω.1), ω.2.1)
  invFun y := ((φ.symm y.1).2, y.2, (φ.symm y.1).1)
  left_inv := fun ⟨s, x, c⟩ => by simp
  right_inv := fun ⟨a, x⟩ => by simp

private theorem actOf_psiL_apply {A T Q X : Type} [Group A] [Group T] (j : T →* A)
    (φ : Q × T ≃ A) (hφ : ∀ (c : Q) (s s' : T), φ (c, s * s') = φ (c, s) * j s') (s : T)
    (ω : T × Q × X) : actOf (psiL φ) (j s) ω = (ω.1 * s⁻¹, ω.2) := by
  rw [actOf_apply_eq_iff]
  simp [psiL, hφ]

private theorem actOf_psiR_apply {A T Q X : Type} [Group A] [Group T] (j : T →* A)
    (φ : Q × T ≃ A) (hφ : ∀ (c : Q) (s s' : T), φ (c, s * s') = φ (c, s) * j s') (s : T)
    (ω : T × X × Q) : actOf (psiR φ) (j s) ω = (ω.1 * s⁻¹, ω.2) := by
  rw [actOf_apply_eq_iff]
  simp [psiR, hφ]

theorem exists_finite_embedding {G : Type} [Group G] {G₁ G₂ T : Subgroup G}
    [Finite G₁] [Finite G₂] (hT₁ : T ≤ G₁) (hT₂ : T ≤ G₂) :
    ∃ (F : Type) (_ : Group F) (_ : Finite F) (ι₁ : ↥G₁ →* F) (ι₂ : ↥G₂ →* F),
      Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      ∀ (t : G) (ht : t ∈ T), ι₁ ⟨t, hT₁ ht⟩ = ι₂ ⟨t, hT₂ ht⟩ := by
  obtain ⟨Q₁, φ₁, hφ₁⟩ :=
    exists_transversal_equiv (Subgroup.inclusion hT₁) (Subgroup.inclusion_injective hT₁)
  obtain ⟨Q₂, φ₂, hφ₂⟩ :=
    exists_transversal_equiv (Subgroup.inclusion hT₂) (Subgroup.inclusion_injective hT₂)
  have : Finite T := Finite.of_injective _ (Subgroup.inclusion_injective hT₁)
  have : Finite Q₁ := Finite.of_injective (fun c : Q₁ => φ₁ (c, 1)) fun c c' h => by
    simpa using φ₁.injective h
  have : Finite Q₂ := Finite.of_injective (fun c : Q₂ => φ₂ (c, 1)) fun c c' h => by
    simpa using φ₂.injective h
  have : Nonempty Q₁ := ⟨(φ₁.symm 1).1⟩
  have : Nonempty Q₂ := ⟨(φ₂.symm 1).1⟩
  refine ⟨Equiv.Perm (T × Q₁ × Q₂), inferInstance, inferInstance, actOf (psiL φ₁),
    actOf (psiR φ₂), actOf_injective _, actOf_injective _, fun t ht => Equiv.ext fun ω => ?_⟩
  exact (actOf_psiL_apply (Subgroup.inclusion hT₁) φ₁ hφ₁ ⟨t, ht⟩ ω).trans
    (actOf_psiR_apply (Subgroup.inclusion hT₂) φ₂ hφ₂ ⟨t, ht⟩ ω).symm

private theorem map_subgroupOf_le {G : Type} [Group G] {G₁ G₂ T : Subgroup G} {F : Type}
    [Group F] (hT₁ : T ≤ G₁) (hT₂ : T ≤ G₂) {ι₁ : ↥G₁ →* F} {ι₂ : ↥G₂ →* F}
    (hagree : ∀ (t : G) (ht : t ∈ T), ι₁ ⟨t, hT₁ ht⟩ = ι₂ ⟨t, hT₂ ht⟩)
    {K : Subgroup G} (hKT : K ≤ T) :
    (K.subgroupOf G₁).map ι₁ ≤ (K.subgroupOf G₂).map ι₂ := by
  rintro y ⟨x, hx, rfl⟩
  have hxK : (x : G) ∈ K := Subgroup.mem_subgroupOf.1 hx
  exact ⟨⟨x, hT₂ (hKT hxK)⟩, hxK, (hagree x (hKT hxK)).symm⟩

theorem map_subgroupOf_eq {G : Type} [Group G] {G₁ G₂ T : Subgroup G} {F : Type} [Group F]
    (hT₁ : T ≤ G₁) (hT₂ : T ≤ G₂) {ι₁ : ↥G₁ →* F} {ι₂ : ↥G₂ →* F}
    (hagree : ∀ (t : G) (ht : t ∈ T), ι₁ ⟨t, hT₁ ht⟩ = ι₂ ⟨t, hT₂ ht⟩)
    {K : Subgroup G} (hKT : K ≤ T) :
    (K.subgroupOf G₁).map ι₁ = (K.subgroupOf G₂).map ι₂ :=
  le_antisymm (map_subgroupOf_le hT₁ hT₂ hagree hKT)
    (map_subgroupOf_le hT₂ hT₁ (fun t ht => (hagree t ht).symm) hKT)

theorem exists_of_le_map {G : Type} [Group G] {G₁ T : Subgroup G} {F : Type} [Group F]
    {ι₁ : ↥G₁ →* F} (hι : Function.Injective ι₁) (hT₁ : T ≤ G₁) {N : Subgroup F}
    (hN : N ≤ (T.subgroupOf G₁).map ι₁) :
    ∃ K : Subgroup G, K ≤ T ∧ N = (K.subgroupOf G₁).map ι₁ := by
  have hle : N.comap ι₁ ≤ T.subgroupOf G₁ := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hN hx
    obtain rfl : y = x := hι hxy
    exact hy
  refine ⟨(N.comap ι₁).map G₁.subtype, ?_, ?_⟩
  · calc (N.comap ι₁).map G₁.subtype ≤ (T.subgroupOf G₁).map G₁.subtype := Subgroup.map_mono hle
      _ = T ⊓ G₁ := Subgroup.subgroupOf_map_subtype T G₁
      _ = T := inf_of_le_left hT₁
  · have h : ((N.comap ι₁).map G₁.subtype).subgroupOf G₁ = N.comap ι₁ :=
      Subgroup.comap_map_eq_self_of_injective G₁.subtype_injective _
    rw [h]
    exact (Subgroup.map_comap_eq_self (hN.trans (Subgroup.map_le_range _ _))).symm

end CFSG.Quasithin.SimsD1.Embed
