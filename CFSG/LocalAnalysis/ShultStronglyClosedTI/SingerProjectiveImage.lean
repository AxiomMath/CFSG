module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SingerScalar
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Data.Fintype.CardEmbedding

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.Singer

open scoped LinearAlgebra.Projectivization Pointwise
open Projectivization Module MulAction

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

abbrev projectiveImage (G : Subgroup (F ≃ₗ[k] F)) : Subgroup (Equiv.Perm (ℙ k F)) :=
  G.map (MulAction.toPermHom (F ≃ₗ[k] F) (ℙ k F))

@[expose] def kScalarsTo (G : Subgroup (F ≃ₗ[k] F)) (hS : scalars k F ≤ G) : kˣ →* G :=
  MonoidHom.codRestrict ((scalarHom k F).comp (Units.map (algebraMap k F : k →* F))) G
    fun _ => hS (scalarHom_mem_scalars _)

theorem kScalarsTo_injective (G : Subgroup (F ≃ₗ[k] F)) (hS : scalars k F ≤ G) :
    Function.Injective (kScalarsTo G hS) := by
  intro c d h
  have h1 := congrArg (fun g : G => (g : F ≃ₗ[k] F) 1) h
  simp only [kScalarsTo, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, scalarHom_apply,
    mul_one, Units.coe_map] at h1
  exact Units.ext ((algebraMap k F).injective h1)

theorem card_eq_card_projectiveImage_mul (G : Subgroup (F ≃ₗ[k] F))
    (hS : scalars k F ≤ G) :
    Nat.card G = Nat.card (projectiveImage G) * (Nat.card k - 1) := by
  set f := (MulAction.toPermHom (F ≃ₗ[k] F) (ℙ k F)).comp G.subtype
  have hrange : f.range = projectiveImage G := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = (kScalarsTo G hS).range := by
    ext g
    rw [MonoidHom.mem_ker]
    constructor
    · intro hg
      have hfix : ∀ p : ℙ k F, (g : F ≃ₗ[k] F) • p = p := fun p => by
        have := congrArg (fun σ : Equiv.Perm (ℙ k F) => σ p) hg
        exact this
      obtain ⟨c, hc0, hc⟩ := exists_eq_algebraMap_of_forall_smul_eq hfix
      refine ⟨Units.mk0 c hc0, Subtype.ext (LinearEquiv.ext fun x => ?_)⟩
      simp only [kScalarsTo, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, scalarHom_apply,
        Units.coe_map, Units.val_mk0]
      exact (hc x).symm
    · rintro ⟨c, rfl⟩
      refine Equiv.ext fun p => ?_
      change scalarHom k F (Units.map (algebraMap k F : k →* F) c) • p = p
      rw [scalarHom_smul]
      exact units_smul_eq_self_iff.mpr ⟨c, rfl⟩
  have h1 := f.ker.card_mul_index
  rw [Subgroup.index_ker, hrange, hker,
    Nat.card_congr (MonoidHom.ofInjective (kScalarsTo_injective G hS)).symm.toEquiv,
    Nat.card_units] at h1
  rw [← h1, mul_comm]

theorem isPreprimitive_projectiveImage (G : Subgroup (F ≃ₗ[k] F))
    [IsPreprimitive G (ℙ k F)] : IsPreprimitive (projectiveImage G) (ℙ k F) := by
  let f : ℙ k F →ₑ[(MulAction.toPermHom (F ≃ₗ[k] F) (ℙ k F)).subgroupMap G] ℙ k F :=
    { toFun := id
      map_smul' := fun _ _ => rfl }
  exact IsPreprimitive.of_surjective (f := f) Function.surjective_id

theorem isPretransitive_projectiveImage_scalars :
    IsPretransitive (projectiveImage (scalars k F)) (ℙ k F) := by
  refine ⟨fun p q => ?_⟩
  obtain ⟨c, hc⟩ := exists_units_smul_eq p q
  refine ⟨⟨_, ⟨scalarHom k F c, scalarHom_mem_scalars c, rfl⟩⟩, ?_⟩
  change scalarHom k F c • p = q
  rw [scalarHom_smul, hc]

theorem stabilizer_projectiveImage_scalars (p : ℙ k F) :
    stabilizer (projectiveImage (scalars k F)) p = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro ⟨σ, s, ⟨c, rfl⟩, rfl⟩ hσ
  have hfix : c • p = p := by
    rw [← scalarHom_smul]
    exact MulAction.mem_stabilizer_iff.mp hσ
  have hk := units_smul_eq_self_iff.mp hfix
  refine Subtype.ext (Equiv.ext fun q => ?_)
  change scalarHom k F c • q = q
  rw [scalarHom_smul]
  exact units_smul_eq_self_iff.mpr hk

instance isCyclic_projectiveImage_scalars [Finite F] :
    IsCyclic (projectiveImage (scalars k F)) := by
  have hrange : projectiveImage (scalars k F) =
      ((MulAction.toPermHom (F ≃ₗ[k] F) (ℙ k F)).comp (scalarHom k F)).range := by
    rw [MonoidHom.range_comp]
    rfl
  rw [hrange]
  exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)

theorem projectiveImage_mono {G H : Subgroup (F ≃ₗ[k] F)} (h : G ≤ H) :
    projectiveImage G ≤ projectiveImage H :=
  Subgroup.map_mono h

theorem mul_pred_dvd_card {G Ω : Type*} [Group G] [MulAction G Ω] [Finite Ω]
    (h2 : IsMultiplyPretransitive G Ω 2) (hΩ : 2 ≤ Nat.card Ω) :
    Nat.card Ω * (Nat.card Ω - 1) ∣ Nat.card G := by
  have : Fintype Ω := Fintype.ofFinite Ω
  obtain ⟨x⟩ : Nonempty (Fin 2 ↪ Ω) := by
    rw [← Fintype.card_fin 2, Nat.card_eq_fintype_card] at hΩ
    exact Function.Embedding.nonempty_of_card_le hΩ
  have hidx := MulAction.index_stabilizer_of_transitive G x
  rw [Nat.card_eq_fintype_card (α := Fin 2 ↪ Ω), Fintype.card_embedding_eq, Fintype.card_fin,
    ← Nat.card_eq_fintype_card] at hidx
  have hd : (Nat.card Ω).descFactorial 2 = Nat.card Ω * (Nat.card Ω - 1) := by
    simp [Nat.descFactorial, mul_comm]
  rw [hd] at hidx
  rw [← hidx]
  exact Subgroup.index_dvd_card _

theorem normalizes_of_normal {G : Subgroup (F ≃ₗ[k] F)} (hS : scalars k F ≤ G)
    (hN : ((projectiveImage (scalars k F)).subgroupOf (projectiveImage G)).Normal)
    {g : F ≃ₗ[k] F} (hg : g ∈ G) (c : Fˣ) : ∃ c' : Fˣ, ∀ x, g (c * x) = c' * g x := by
  set ρ := MulAction.toPermHom (F ≃ₗ[k] F) (ℙ k F)
  have hmem := hN.conj_mem ⟨ρ (scalarHom k F c),
      projectiveImage_mono hS ⟨_, scalarHom_mem_scalars c, rfl⟩⟩
    (by rw [Subgroup.mem_subgroupOf]; exact ⟨_, scalarHom_mem_scalars c, rfl⟩)
    ⟨ρ g, ⟨g, hg, rfl⟩⟩
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨s, ⟨c', rfl⟩, hs⟩ := hmem
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hs
  set h := (scalarHom k F c')⁻¹ * (g * scalarHom k F c * g⁻¹)
  have hfix : ∀ p : ℙ k F, h • p = p := fun p => by
    have := congrArg (fun σ : Equiv.Perm (ℙ k F) => σ p) hs
    simp only [ρ, MulAction.toPermHom_apply, Equiv.Perm.mul_apply,
      MulAction.toPerm_apply, Equiv.Perm.inv_def, MulAction.toPerm_symm_apply] at this
    simp only [h, mul_smul, ← this, inv_smul_smul]
  obtain ⟨r, hr0, hr⟩ := exists_eq_algebraMap_of_forall_smul_eq hfix
  refine ⟨c' * Units.mk0 (algebraMap k F r) (by simpa using hr0), fun x => ?_⟩
  have hx := hr (g x)
  simp only [h, LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply,
    scalarHom_apply] at hx
  have hc' : g (c * x) = c' * (algebraMap k F r * g x) := by
    rw [← hx]
    exact (LinearEquiv.apply_symm_apply (scalarHom k F c') _).symm
  rw [hc', Units.val_mul, Units.val_mk0, mul_assoc]

theorem card_le_of_normalizes [Finite F] (G : Subgroup (F ≃ₗ[k] F))
    (hG : ∀ g ∈ G, ∀ c : Fˣ, ∃ c' : Fˣ, ∀ x, g (c * x) = c' * g x) :
    Nat.card G ≤ (Nat.card F - 1) * finrank k F := by
  have : FiniteDimensional k F := Module.Finite.of_finite
  have hsemi : ∀ g ∈ G, ∃ σ : F ≃ₐ[k] F, ∀ a x, g (a * x) = σ a * g x := by
    intro g hg
    obtain ⟨σ, hσ⟩ := exists_algEquiv_of_normalizes ⊤ g (by
      intro a _
      by_cases ha : a = 0
      · exact ⟨0, IntermediateField.zero_mem _, fun x => by rw [ha, zero_mul, map_zero, zero_mul]⟩
      · obtain ⟨c', hc'⟩ := hG g hg (Units.mk0 a ha)
        exact ⟨c', IntermediateField.mem_top, hc'⟩)
    refine ⟨(IntermediateField.topEquiv.symm.trans σ).trans IntermediateField.topEquiv,
      fun a x => ?_⟩
    have := hσ ⟨a, IntermediateField.mem_top⟩ x
    exact this
  choose! σ hσ using hsemi
  have hg1 : ∀ g : F ≃ₗ[k] F, g 1 ≠ 0 := fun g h => one_ne_zero (g.injective (h.trans g.map_zero.symm))
  let φ : G → (F ≃ₐ[k] F) × Fˣ := fun g => (σ g, Units.mk0 ((g : F ≃ₗ[k] F) 1) (hg1 g))
  have hφ : Function.Injective φ := by
    intro g h hgh
    simp only [φ, Prod.mk.injEq] at hgh
    refine Subtype.ext (LinearEquiv.ext fun x => ?_)
    have h1 := hσ g g.2 x 1
    have h2 := hσ h h.2 x 1
    rw [mul_one] at h1 h2
    have hgh1 : (g : F ≃ₗ[k] F) 1 = (h : F ≃ₗ[k] F) 1 := by
      simpa using congrArg Units.val hgh.2
    rw [h1, h2, hgh.1, hgh1]
  have := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card (α := F ≃ₐ[k] F)] at this
  calc Nat.card G ≤ Fintype.card (F ≃ₐ[k] F) * (Nat.card F - 1) := this
    _ ≤ finrank k F * (Nat.card F - 1) := Nat.mul_le_mul_right _ AlgEquiv.card_le
    _ = (Nat.card F - 1) * finrank k F := mul_comm _ _

theorem card_linearEquiv_of_finrank_eq_two [Finite F] (h : finrank k F = 2) :
    Nat.card (F ≃ₗ[k] F) = (Nat.card k ^ 2 - 1) * (Nat.card k ^ 2 - Nat.card k) := by
  have : FiniteDimensional k F := Module.Finite.of_finite
  have : Finite k := Finite.of_injective _ (algebraMap k F).injective
  have : Fintype k := Fintype.ofFinite k
  let basis : Module.Basis (Fin 2) k F := Module.finBasisOfFinrankEq k F h
  let glEquiv : GL (Fin 2) k ≃* (F ≃ₗ[k] F) :=
    (Matrix.GeneralLinearGroup.toLin' basis).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k F)
  rw [← Nat.card_congr glEquiv.toEquiv, Matrix.card_GL_field, Fin.prod_univ_two,
    Fintype.card_eq_nat_card]
  simp

section restrict

variable (k) (l : IntermediateField k F)

@[expose] def restrictScalarsHom : (F ≃ₗ[l] F) →* (F ≃ₗ[k] F) where
  toFun g := g.restrictScalars k
  map_one' := rfl
  map_mul' _ _ := rfl

variable {k} {l}

theorem restrictScalarsHom_apply (g : F ≃ₗ[l] F) (x : F) :
    restrictScalarsHom k l g x = g x :=
  rfl

theorem restrictScalarsHom_injective : Function.Injective (restrictScalarsHom k l) := by
  intro g h hgh
  exact LinearEquiv.ext fun x => LinearEquiv.congr_fun hgh x

theorem exists_restrictScalarsHom_eq {g : F ≃ₗ[k] F} (hg : ∀ (a : l) (x : F), g (a * x) = a * g x) :
    ∃ g' : F ≃ₗ[l] F, restrictScalarsHom k l g' = g :=
  ⟨g.toAddEquiv.toLinearEquiv fun a x => hg a x, LinearEquiv.ext fun _ => rfl⟩

theorem restrictScalarsHom_scalarHom (c : Fˣ) :
    restrictScalarsHom k l (scalarHom l F c) = scalarHom k F c :=
  LinearEquiv.ext fun _ => rfl

end restrict

theorem exists_card_eq_mul_of_semilinear [Finite F] (G : Subgroup (F ≃ₗ[k] F))
    (l : IntermediateField k F)
    (hσ : ∀ g ∈ G, ∃ σ : l ≃ₐ[k] l, ∀ (a : l) (x : F), g (a * x) = σ a * g x) :
    ∃ G₁ : Subgroup (F ≃ₗ[k] F), G₁ ≤ G ∧
      (∀ g ∈ G₁, ∀ (a : l) (x : F), g (a * x) = a * g x) ∧
      (∀ g ∈ G, (∀ (a : l) (x : F), g (a * x) = a * g x) → g ∈ G₁) ∧
      ∃ h, h ≤ finrank k l ∧ Nat.card G = Nat.card G₁ * h := by
  have : FiniteDimensional k F := Module.Finite.of_finite
  have hg1 : ∀ g : F ≃ₗ[k] F, g 1 ≠ 0 := fun g h => one_ne_zero (g.injective (h.trans g.map_zero.symm))
  have huniq : ∀ (g : F ≃ₗ[k] F) (σ τ : l ≃ₐ[k] l), (∀ (a : l) (x : F), g (a * x) = σ a * g x) →
      (∀ (a : l) (x : F), g (a * x) = τ a * g x) → σ = τ := by
    intro g σ τ hσg hτg
    ext a
    have h1 := (hσg a 1).symm.trans (hτg a 1)
    exact mul_right_cancel₀ (hg1 g) h1
  choose! Φ hΦ using hσ
  let Φhom : G →* (l ≃ₐ[k] l) :=
    { toFun := fun g => Φ g
      map_one' := huniq 1 _ _ (hΦ 1 G.one_mem) (fun a x => by simp)
      map_mul' := fun g h => huniq (g * h) _ _ (hΦ _ (G.mul_mem g.2 h.2)) (fun a x => by
        simp only [LinearEquiv.mul_apply, AlgEquiv.mul_apply]
        rw [hΦ h h.2, hΦ g g.2]) }
  set G₁ : Subgroup (F ≃ₗ[k] F) := Φhom.ker.map G.subtype
  have hmem : ∀ g ∈ G, (g ∈ G₁ ↔ ∀ (a : l) (x : F), g (a * x) = a * g x) := by
    intro g hg
    constructor
    · rintro ⟨g', hg', rfl⟩ a x
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hg'
      have := hΦ g' g'.2 a x
      change (g' : F ≃ₗ[k] F) (a * x) = a * (g' : F ≃ₗ[k] F) x
      rw [this]
      change (Φhom g' a : F) * _ = _
      rw [hg']
      rfl
    · intro hlin
      refine ⟨⟨g, hg⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      exact huniq g _ _ (hΦ g hg) (fun a x => by rw [hlin]; rfl)
  refine ⟨G₁, fun g hg => ?_, fun g hg => ?_, fun g hg hlin => (hmem g hg).mpr hlin,
    Φhom.ker.index, ?_, ?_⟩
  · obtain ⟨g', -, rfl⟩ := hg
    exact g'.2
  · have hgG : g ∈ G := by
      obtain ⟨g', -, rfl⟩ := hg
      exact g'.2
    exact (hmem g hgG).mp hg
  · rw [Subgroup.index_ker]
    calc Nat.card Φhom.range ≤ Nat.card (l ≃ₐ[k] l) := Subgroup.card_le_card_group _
      _ = Fintype.card (l ≃ₐ[k] l) := Nat.card_eq_fintype_card
      _ ≤ finrank k l := AlgEquiv.card_le
  · rw [Subgroup.card_map_of_injective G.subtype_injective, Subgroup.card_mul_index]

end CFSG.ShultStronglyClosedTI.Singer
