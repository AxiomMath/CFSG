module

public import CFSG.Quasithin.H13.QRCPairedFactors
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism
public import CFSG.Quasithin.H13.QRCPairLift

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField CFSG.GorensteinWalter
  CFSG.Glauberman.Dickson CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.MatrixGroups
open scoped MatrixGroups

section SLMap

variable {k : Type} [Field k]

theorem sl_map_mul (σ τ : RingAut k) (g : SL(2, k)) :
    Matrix.SpecialLinearGroup.map (σ * τ).toRingHom g =
      Matrix.SpecialLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.map τ.toRingHom g) := by
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem sl_map_one (g : SL(2, k)) :
    Matrix.SpecialLinearGroup.map (1 : RingAut k).toRingHom g = g := by
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

theorem sl_map_inv_map (σ : RingAut k) (g : SL(2, k)) :
    Matrix.SpecialLinearGroup.map σ⁻¹.toRingHom (Matrix.SpecialLinearGroup.map σ.toRingHom g) =
      g := by
  rw [← sl_map_mul, inv_mul_cancel, sl_map_one]

theorem sl2_upperUnipotent_one_ne_one : sl2UpperUnipotent (1 : k) ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : SL(2, k) => (g : Matrix (Fin 2) (Fin 2) k) 0 1) h
  simp [sl2UpperUnipotent] at h1

end SLMap

section Coord

variable {A : Type*} [Group A] {k : Type} [Field k]

theorem map_conj_eq_of_mem_normalizer' {X : Subgroup A} {g : A}
    (hg : g ∈ normalizer (X : Set A)) : X.map (MulAut.conj g).toMonoidHom = X := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hg x).1 hx
  · intro x hx
    refine ⟨g⁻¹ * x * g, (mem_normalizer_iff.1 hg _).2 ?_, ?_⟩
    · rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem map_conj_mul (X : Subgroup A) (a b : A) :
    X.map (MulAut.conj (a * b)).toMonoidHom =
      (X.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext y
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

@[expose] noncomputable def conjEquiv (a : A) {X Y : Subgroup A}
    (h : X.map (MulAut.conj a).toMonoidHom = Y) : X ≃* Y :=
  (X.equivMapOfInjective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective).trans
    (MulEquiv.subgroupCongr h)

theorem coe_conjEquiv (a : A) {X Y : Subgroup A} (h : X.map (MulAut.conj a).toMonoidHom = Y)
    (x : X) : (conjEquiv a h x : A) = a * x * a⁻¹ := rfl

@[expose] def ActsAsField {X Y : Subgroup A} (θ : X ≃* SL(2, k)) (θ' : Y ≃* SL(2, k)) (a : A)
    (σ : RingAut k) : Prop :=
  X.map (MulAut.conj a).toMonoidHom = Y ∧ ∀ (x : X) (y : Y), (y : A) = a * x * a⁻¹ →
    θ' y = Matrix.SpecialLinearGroup.map σ.toRingHom (θ x)

namespace ActsAsField

variable {X Y Z : Subgroup A} {θ : X ≃* SL(2, k)} {θ' : Y ≃* SL(2, k)} {θ'' : Z ≃* SL(2, k)}

theorem mem {a : A} {σ : RingAut k} (h : ActsAsField θ θ' a σ) {x : A} (hx : x ∈ X) :
    a * x * a⁻¹ ∈ Y := by
  rw [← h.1]
  exact ⟨x, hx, rfl⟩

theorem apply {a : A} {σ : RingAut k} (h : ActsAsField θ θ' a σ) (x : X) :
    θ' ⟨a * x * a⁻¹, h.mem x.2⟩ = Matrix.SpecialLinearGroup.map σ.toRingHom (θ x) :=
  h.2 x _ rfl

theorem mul {a b : A} {σ τ : RingAut k} (h₁ : ActsAsField θ' θ'' a σ)
    (h₂ : ActsAsField θ θ' b τ) : ActsAsField θ θ'' (a * b) (σ * τ) := by
  refine ⟨?_, fun x z hz => ?_⟩
  · rw [← h₁.1, ← h₂.1, map_conj_mul]
  · have hz' : (z : A) = a * (⟨b * x * b⁻¹, h₂.mem x.2⟩ : Y) * a⁻¹ := by
      rw [hz]
      change a * b * (x : A) * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹
      group
    rw [h₁.2 _ z hz', h₂.apply, sl_map_mul]

theorem inv {a : A} {σ : RingAut k} (h : ActsAsField θ θ' a σ) : ActsAsField θ' θ a⁻¹ σ⁻¹ := by
  refine ⟨?_, fun y x hx => ?_⟩
  · rw [← h.1, ← map_conj_mul, inv_mul_cancel]
    have : (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A := by
      ext y
      simp
    rw [this, map_id]
  · have hy : (y : A) = a * x * a⁻¹ := by
      rw [hx]
      group
    rw [h.2 x y hy, sl_map_inv_map]

theorem one : ActsAsField θ θ (1 : A) 1 := by
  refine ⟨?_, fun x y hy => ?_⟩
  · have : (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A := by
      ext y
      simp
    rw [this, map_id]
  · have : y = x := Subtype.ext (by rw [hy]; group)
    rw [this, sl_map_one]

theorem conj {a c : A} {σ : RingAut k} (h : ActsAsField θ θ' a σ)
    (hX : X.map (MulAut.conj c⁻¹).toMonoidHom = X) (hY : Y.map (MulAut.conj c⁻¹).toMonoidHom = Y) :
    ActsAsField ((conjEquiv c⁻¹ hX).trans θ) ((conjEquiv c⁻¹ hY).trans θ') (c * a * c⁻¹) σ := by
  have hXc : X.map (MulAut.conj c).toMonoidHom = X := by
    conv_lhs => rw [← hX]
    rw [← map_conj_mul, mul_inv_cancel]
    have : (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A := by
      ext y
      simp
    rw [this, map_id]
  have hYc : Y.map (MulAut.conj c).toMonoidHom = Y := by
    conv_lhs => rw [← hY]
    rw [← map_conj_mul, mul_inv_cancel]
    have : (MulAut.conj (1 : A)).toMonoidHom = MonoidHom.id A := by
      ext y
      simp
    rw [this, map_id]
  refine ⟨?_, fun x y hy => ?_⟩
  · rw [map_conj_mul, map_conj_mul, hX, h.1, hYc]
  · simp only [MulEquiv.trans_apply]
    refine h.2 _ _ ?_
    rw [coe_conjEquiv, coe_conjEquiv, hy]
    group

end ActsAsField

variable {K₁ K₂ : Subgroup A}

@[expose] def IsFieldPerm (θ₁ : K₁ ≃* SL(2, k)) (θ₂ : K₂ ≃* SL(2, k)) (a : A) : Prop :=
  ∃ σ₁ σ₂ : RingAut k, (ActsAsField θ₁ θ₁ a σ₁ ∧ ActsAsField θ₂ θ₂ a σ₂) ∨
    (ActsAsField θ₁ θ₂ a σ₁ ∧ ActsAsField θ₂ θ₁ a σ₂)

@[expose] def fieldPermGroup (θ₁ : K₁ ≃* SL(2, k)) (θ₂ : K₂ ≃* SL(2, k)) : Subgroup A where
  carrier := {a | IsFieldPerm θ₁ θ₂ a}
  mul_mem' := by
    rintro a b ⟨σ₁, σ₂, ⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩⟩ ⟨τ₁, τ₂, ⟨hb₁, hb₂⟩ | ⟨hb₁, hb₂⟩⟩
    · exact ⟨σ₁ * τ₁, σ₂ * τ₂, Or.inl ⟨ha₁.mul hb₁, ha₂.mul hb₂⟩⟩
    · exact ⟨σ₂ * τ₁, σ₁ * τ₂, Or.inr ⟨ha₂.mul hb₁, ha₁.mul hb₂⟩⟩
    · exact ⟨σ₁ * τ₁, σ₂ * τ₂, Or.inr ⟨ha₁.mul hb₁, ha₂.mul hb₂⟩⟩
    · exact ⟨σ₂ * τ₁, σ₁ * τ₂, Or.inl ⟨ha₂.mul hb₁, ha₁.mul hb₂⟩⟩
  one_mem' := ⟨1, 1, Or.inl ⟨ActsAsField.one, ActsAsField.one⟩⟩
  inv_mem' := by
    rintro a ⟨σ₁, σ₂, ⟨ha₁, ha₂⟩ | ⟨ha₁, ha₂⟩⟩
    · exact ⟨σ₁⁻¹, σ₂⁻¹, Or.inl ⟨ha₁.inv, ha₂.inv⟩⟩
    · exact ⟨σ₂⁻¹, σ₁⁻¹, Or.inr ⟨ha₂.inv, ha₁.inv⟩⟩

@[expose] def stdSub {X : Subgroup A} (θ : X ≃* SL(2, k)) (Z : Subgroup SL(2, k)) : Subgroup A :=
  (Z.map θ.symm.toMonoidHom).map X.subtype

theorem mem_stdSub {X : Subgroup A} {θ : X ≃* SL(2, k)} {Z : Subgroup SL(2, k)} {x : A} :
    x ∈ stdSub θ Z ↔ ∃ hx : x ∈ X, θ ⟨x, hx⟩ ∈ Z := by
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨(θ.symm z).2, ?_⟩
    change θ (θ.symm z) ∈ Z
    rw [MulEquiv.apply_symm_apply]
    exact hz
  · rintro ⟨hx, hz⟩
    exact ⟨⟨x, hx⟩, ⟨θ ⟨x, hx⟩, hz, by simp⟩, rfl⟩

theorem stdSub_le {X : Subgroup A} (θ : X ≃* SL(2, k)) (Z : Subgroup SL(2, k)) :
    stdSub θ Z ≤ X :=
  map_subtype_le _

theorem stdSub_mono {X : Subgroup A} (θ : X ≃* SL(2, k)) {Z Z' : Subgroup SL(2, k)}
    (h : Z ≤ Z') : stdSub θ Z ≤ stdSub θ Z' :=
  map_mono (map_mono h)

theorem stdSub_top {X : Subgroup A} (θ : X ≃* SL(2, k)) : stdSub θ ⊤ = X := by
  rw [stdSub, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 θ.symm.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

theorem ActsAsField.conj_mem_stdSub {X Y : Subgroup A} {θ : X ≃* SL(2, k)} {θ' : Y ≃* SL(2, k)}
    {a : A} {σ : RingAut k} (h : ActsAsField θ θ' a σ) {Z : Subgroup SL(2, k)}
    (hZ : ∀ g ∈ Z, Matrix.SpecialLinearGroup.map σ.toRingHom g ∈ Z) {x : A}
    (hx : x ∈ stdSub θ Z) : a * x * a⁻¹ ∈ stdSub θ' Z := by
  obtain ⟨hxX, hxZ⟩ := mem_stdSub.1 hx
  refine mem_stdSub.2 ⟨h.mem hxX, ?_⟩
  rw [h.apply ⟨x, hxX⟩]
  exact hZ _ hxZ

theorem coe_symm_mem_stdSub {X : Subgroup A} (θ : X ≃* SL(2, k)) {Z : Subgroup SL(2, k)}
    {g : SL(2, k)} (hg : g ∈ Z) : ((θ.symm g : X) : A) ∈ stdSub θ Z :=
  ⟨θ.symm g, ⟨g, hg, rfl⟩, rfl⟩

variable {n : ℕ}

theorem exists_semilinear (hk : Nat.card k = 2 ^ n) {X Y : Subgroup A} (θ : X ≃* SL(2, k))
    (θ' : Y ≃* SL(2, k)) (φ : X ≃* Y) :
    ∃ (g : SL(2, k)) (σ : RingAut k), ∀ x : X,
      θ' (φ x) = g * Matrix.SpecialLinearGroup.map σ.toRingHom (θ x) * g⁻¹ := by
  obtain ⟨γ, hγ⟩ := (gammaToMulAut_bijective_of_card hk).2 (θ.symm.trans (φ.trans θ'))
  refine ⟨γ.left, γ.right, fun x => ?_⟩
  have h1 := congrArg (fun α : MulAut SL(2, k) => α (θ x)) hγ
  simp only [gammaToMulAut_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  exact h1.symm

theorem semilinear_unique (hk : Nat.card k = 2 ^ n) {h₁ h₂ : SL(2, k)} {σ τ : RingAut k}
    (h : ∀ g, h₁ * Matrix.SpecialLinearGroup.map σ.toRingHom g * h₁⁻¹ =
      h₂ * Matrix.SpecialLinearGroup.map τ.toRingHom g * h₂⁻¹) : h₁ = h₂ ∧ σ = τ := by
  have := (gammaToMulAut_bijective_of_card hk).1 (a₁ := ⟨h₁, σ⟩) (a₂ := ⟨h₂, τ⟩)
    (MulEquiv.ext fun g => by simp only [gammaToMulAut_apply]; exact h g)
  exact ⟨congrArg SemidirectProduct.left this, congrArg SemidirectProduct.right this⟩

theorem eq_one_of_actsAsField (hk : Nat.card k = 2 ^ n) {X : Subgroup A} {θ : X ≃* SL(2, k)}
    {a c : A} {σ : RingAut k} (h : ActsAsField θ θ a σ) (hc : c ∈ X)
    (hac : ∀ x ∈ X, a * x * a⁻¹ = c * x * c⁻¹) : c = 1 := by
  have key : ∀ g, θ ⟨c, hc⟩ * Matrix.SpecialLinearGroup.map (1 : RingAut k).toRingHom g *
      (θ ⟨c, hc⟩)⁻¹ = 1 * Matrix.SpecialLinearGroup.map σ.toRingHom g * 1⁻¹ := by
    intro g
    rw [sl_map_one, one_mul, inv_one, mul_one]
    obtain ⟨x, rfl⟩ := θ.surjective g
    rw [← h.apply x]
    have : (⟨a * x * a⁻¹, h.mem x.2⟩ : X) = ⟨c, hc⟩ * x * ⟨c, hc⟩⁻¹ :=
      Subtype.ext (hac x x.2)
    rw [this, map_mul, map_mul, map_inv]
  have h1 := (semilinear_unique hk key).1
  have h2 : (⟨c, hc⟩ : X) = 1 := by
    rw [← θ.map_eq_one_iff]
    exact h1
  exact congrArg Subtype.val h2

section Product

variable (hk : Nat.card k = 2 ^ n) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
  (hd : K₁ ⊓ K₂ = ⊥)
include hk hc hd

theorem sup_inf_fieldPermGroup_eq_bot (θ₁ : K₁ ≃* SL(2, k)) (θ₂ : K₂ ≃* SL(2, k)) :
    (K₁ ⊔ K₂) ⊓ fieldPermGroup θ₁ θ₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro a ⟨haK, σ₁, σ₂, ⟨h₁, h₂⟩ | ⟨h₁, -⟩⟩
  · obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := exists_mul_of_mem_sup_of_commute hc haK
    have e₁ : a₁ = 1 := eq_one_of_actsAsField hk h₁ ha₁ fun x hx => by
      rw [show a₁ * a₂ * x * (a₁ * a₂)⁻¹ = a₁ * (a₂ * x * a₂⁻¹) * a₁⁻¹ by group,
        ← hc x hx a₂ ha₂, mul_inv_cancel_right]
    have e₂ : a₂ = 1 := eq_one_of_actsAsField hk h₂ ha₂ fun y hy => by
      rw [show a₁ * a₂ * y * (a₁ * a₂)⁻¹ = a₁ * (a₂ * y * a₂⁻¹) * a₁⁻¹ by group,
        hc a₁ ha₁ _ (K₂.mul_mem (K₂.mul_mem ha₂ hy) (K₂.inv_mem ha₂)), mul_inv_cancel_right]
    rw [e₁, e₂, mul_one, mem_bot]
  · exfalso
    have hN : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set A) :=
      sup_le le_normalizer (le_normalizer_of_commute hc)
    have h1 := h₁.1
    rw [map_conj_eq_of_mem_normalizer' (hN haK)] at h1
    have h2 : (θ₁.symm (sl2UpperUnipotent 1) : A) ∈ K₁ ⊓ K₂ :=
      ⟨(θ₁.symm _).2, h1 ▸ (θ₁.symm _).2⟩
    rw [hd, mem_bot] at h2
    apply sl2_upperUnipotent_one_ne_one (k := k)
    rw [← θ₁.apply_symm_apply (sl2UpperUnipotent 1)]
    rw [show θ₁.symm (sl2UpperUnipotent 1) = 1 from Subtype.ext h2, map_one]

end Product

theorem ne_bot_of_sl2 {X : Subgroup A} (θ : X ≃* SL(2, k)) : X ≠ ⊥ := by
  intro h
  apply sl2_upperUnipotent_one_ne_one (k := k)
  have h1 : ((θ.symm (sl2UpperUnipotent 1) : X) : A) = 1 :=
    mem_bot.1 (h ▸ (θ.symm (sl2UpperUnipotent 1)).2 :
      ((θ.symm (sl2UpperUnipotent 1) : X) : A) ∈ (⊥ : Subgroup A))
  rw [← θ.apply_symm_apply (sl2UpperUnipotent 1), show θ.symm (sl2UpperUnipotent 1) = 1 from
    Subtype.ext h1, map_one]

theorem eq_one_of_central [CharP k 2] {X : Subgroup A} (θ : X ≃* SL(2, k)) {z : A} (hz : z ∈ X)
    (hcen : ∀ y ∈ X, z * y = y * z) : z = 1 := by
  have h1 : θ ⟨z, hz⟩ ∈ center SL(2, k) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := θ.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcen y y.2).symm
  rw [sl2_center_eq_bot, mem_bot, θ.map_eq_one_iff] at h1
  exact congrArg Subtype.val h1

theorem isSimpleGroup_of_sl2 [CharP k 2] (hk4 : 4 ≤ Nat.card k) {X : Subgroup A}
    (θ : X ≃* SL(2, k)) : IsSimpleGroup X := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) k) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hk4
  exact MulEquiv.isSimpleGroup (θ.trans sl2EquivPSL2)

theorem mem_normalizer_of_commute {Y : Subgroup A} {c : A} (hc : ∀ y ∈ Y, c * y = y * c) :
    c ∈ normalizer (Y : Set A) := by
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => ?_, fun hy => ?_⟩
  · rw [hc y hy, mul_inv_cancel_right]
    exact hy
  · have h1 := hc _ hy
    have h2 : y = c * y * c⁻¹ := by
      calc y = c⁻¹ * ((c * y * c⁻¹) * c) := by group
        _ = c⁻¹ * (c * (c * y * c⁻¹)) := by rw [h1]
        _ = c * y * c⁻¹ := by group
    rw [h2]
    exact hy

theorem actsAsField_of_semilinear {X Y : Subgroup A} {θ : X ≃* SL(2, k)} {θ' : Y ≃* SL(2, k)}
    {a : A} (h : X.map (MulAut.conj a).toMonoidHom = Y) {g : SL(2, k)} {σ : RingAut k}
    (hg : ∀ x : X,
      θ' (conjEquiv a h x) = g * Matrix.SpecialLinearGroup.map σ.toRingHom (θ x) * g⁻¹)
    {cO : A} (hO : ∀ y ∈ Y, cO * y = y * cO) :
    ActsAsField θ θ' ((((θ'.symm g : Y) : A) * cO)⁻¹ * a) σ := by
  set cY : A := ((θ'.symm g : Y) : A) with hcY
  have hcYY : cY ∈ Y := (θ'.symm g).2
  have hcN : (cY * cO)⁻¹ ∈ normalizer (Y : Set A) :=
    inv_mem (mul_mem (le_normalizer hcYY) (mem_normalizer_of_commute hO))
  refine ⟨?_, fun x y hy => ?_⟩
  · rw [map_conj_mul, h, map_conj_eq_of_mem_normalizer' hcN]
  · have hw := hg x
    have hyw : y = (θ'.symm g)⁻¹ * conjEquiv a h x * θ'.symm g := by
      apply Subtype.ext
      rw [hy, coe_mul, coe_mul, coe_inv, coe_conjEquiv, ← hcY]
      have hmem : cY⁻¹ * (a * x * a⁻¹) * cY ∈ Y :=
        Y.mul_mem (Y.mul_mem (Y.inv_mem hcYY) (h ▸ ⟨x, x.2, rfl⟩)) hcYY
      have h1 := hO _ hmem
      calc (cY * cO)⁻¹ * a * x * ((cY * cO)⁻¹ * a)⁻¹ =
          cO⁻¹ * ((cY⁻¹ * (a * x * a⁻¹) * cY) * cO) := by group
        _ = cO⁻¹ * (cO * (cY⁻¹ * (a * x * a⁻¹) * cY)) := by rw [h1]
        _ = cY⁻¹ * (a * x * a⁻¹) * cY := by group
    rw [hyw, map_mul, map_mul, map_inv, hw, MulEquiv.apply_symm_apply]
    group

theorem sup_sup_fieldPermGroup_eq_top [Finite A] [CharP k 2] (hk : Nat.card k = 2 ^ n)
    (hn : 2 ≤ n) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hd : K₁ ⊓ K₂ = ⊥)
    (hKn : (K₁ ⊔ K₂).Normal) (θ₁ : K₁ ≃* SL(2, k)) (θ₂ : K₂ ≃* SL(2, k)) :
    (K₁ ⊔ K₂) ⊔ fieldPermGroup θ₁ θ₂ = ⊤ := by
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hn
  have : IsSimpleGroup K₁ := isSimpleGroup_of_sl2 hk4 θ₁
  have : IsSimpleGroup K₂ := isSimpleGroup_of_sl2 hk4 θ₂
  have hZ₁ : ∀ z ∈ K₁, (∀ y ∈ K₁, z * y = y * z) → z = 1 := fun z hz h =>
    eq_one_of_central θ₁ hz h
  have hZ₂ : ∀ z ∈ K₂, (∀ y ∈ K₂, z * y = y * z) → z = 1 := fun z hz h =>
    eq_one_of_central θ₂ hz h
  have hcard : Nat.card K₁ = Nat.card K₂ :=
    (Nat.card_congr θ₁.toEquiv).trans (Nat.card_congr θ₂.toEquiv).symm
  have hc' : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hKn' : (K₂ ⊔ K₁).Normal := sup_comm K₁ K₂ ▸ hKn
  have hne : K₁ ≠ K₂ := by
    intro h
    apply ne_bot_of_sl2 θ₁
    rw [← hd, ← h, inf_idem]
  rw [eq_top_iff]
  intro a _
  rcases conj_factor_eq_or hc hKn hZ₁ hcard a with h₁ | h₁ <;>
    rcases conj_factor_eq_or hc' hKn' hZ₂ hcard.symm a with h₂ | h₂
  · obtain ⟨g₁, σ₁, hg₁⟩ := exists_semilinear hk θ₁ θ₁ (conjEquiv a h₁)
    obtain ⟨g₂, σ₂, hg₂⟩ := exists_semilinear hk θ₂ θ₂ (conjEquiv a h₂)
    have hc₁ : ((θ₁.symm g₁ : K₁) : A) ∈ K₁ := (θ₁.symm g₁).2
    have hc₂ : ((θ₂.symm g₂ : K₂) : A) ∈ K₂ := (θ₂.symm g₂).2
    have hr : (((θ₁.symm g₁ : K₁) : A) * ((θ₂.symm g₂ : K₂) : A))⁻¹ * a ∈
        fieldPermGroup θ₁ θ₂ := by
      refine ⟨σ₁, σ₂, Or.inl ⟨actsAsField_of_semilinear h₁ hg₁ fun y hy => hc' _ hc₂ y hy, ?_⟩⟩
      rw [hc _ hc₁ _ hc₂]
      exact actsAsField_of_semilinear h₂ hg₂ fun y hy => hc _ hc₁ y hy
    have := mul_mem_sup (mul_mem_sup hc₁ hc₂ : _ ∈ K₁ ⊔ K₂) hr
    rwa [mul_inv_cancel_left] at this
  · exact absurd (map_injective (MulAut.conj a).injective (h₁.trans h₂.symm)) hne
  · exact absurd (map_injective (MulAut.conj a).injective (h₁.trans h₂.symm)) hne
  · obtain ⟨g₁, σ₁, hg₁⟩ := exists_semilinear hk θ₁ θ₂ (conjEquiv a h₁)
    obtain ⟨g₂, σ₂, hg₂⟩ := exists_semilinear hk θ₂ θ₁ (conjEquiv a h₂)
    have hc₁ : ((θ₁.symm g₂ : K₁) : A) ∈ K₁ := (θ₁.symm g₂).2
    have hc₂ : ((θ₂.symm g₁ : K₂) : A) ∈ K₂ := (θ₂.symm g₁).2
    have hr : (((θ₁.symm g₂ : K₁) : A) * ((θ₂.symm g₁ : K₂) : A))⁻¹ * a ∈
        fieldPermGroup θ₁ θ₂ := by
      refine ⟨σ₁, σ₂, Or.inr ⟨?_, actsAsField_of_semilinear h₂ hg₂ fun y hy => hc' _ hc₂ y hy⟩⟩
      rw [hc _ hc₁ _ hc₂]
      exact actsAsField_of_semilinear h₁ hg₁ fun y hy => hc _ hc₁ y hy
    have := mul_mem_sup (mul_mem_sup hc₁ hc₂ : _ ∈ K₁ ⊔ K₂) hr
    rwa [mul_inv_cancel_left] at this

end Coord

end CFSG.Quasithin.H13.QRC
