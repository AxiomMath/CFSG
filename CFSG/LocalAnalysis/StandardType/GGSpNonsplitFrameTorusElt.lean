module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusField
public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord

public section

open Polynomial Module Multiplicative CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType

namespace SpNS

section Mono

variable {K : Type} [Field K] {L : Type} [AddCommGroup L] [Module K L] {s : ℕ} {κ : Type}

@[expose] def monoEquiv (π : Equiv.Perm (Fin s)) (T : Fin s → (L ≃ₗ[K] L)) :
    ((Fin s → L) × (κ → K)) ≃ₗ[K] ((Fin s → L) × (κ → K)) where
  toFun x := (fun i => T i (x.1 (π i)), x.2)
  invFun x := (fun j => (T (π.symm j)).symm (x.1 (π.symm j)), x.2)
  map_add' x y := Prod.ext (funext fun i => map_add (T i) _ _) rfl
  map_smul' c x := Prod.ext (funext fun i => map_smul (T i) c _) rfl
  left_inv x := Prod.ext (funext fun j => by simp) rfl
  right_inv x := Prod.ext (funext fun i => by simp) rfl

theorem monoEquiv_apply (π : Equiv.Perm (Fin s)) (T : Fin s → (L ≃ₗ[K] L)) (d : Fin s → L)
    (w : κ → K) : monoEquiv π T (d, w) = (fun i => T i (d (π i)), w) := rfl

variable {V : Type} [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}
  {Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V} {β : LinearMap.BilinForm K L}

theorem monoEquiv_isom
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (π : Equiv.Perm (Fin s)) {T : Fin s → (L ≃ₗ[K] L)} (hT : ∀ i u v, β (T i u) (T i v) = β u v)
    (x y : (Fin s → L) × (κ → K)) :
    B (Φ (monoEquiv π T x)) (Φ (monoEquiv π T y)) = B (Φ x) (Φ y) := by
  obtain ⟨d, w⟩ := x
  obtain ⟨d', w'⟩ := y
  rw [monoEquiv_apply, monoEquiv_apply,
    hdec (fun i => T i (d (π i))) (fun i => T i (d' (π i))) w w', hdec d d' w w']
  congr 1
  simp only [hT]
  exact Equiv.sum_comp π (fun i => β (d i) (d' i))

end Mono

section Unit

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {X : Type}
  [AddCommGroup X] [Module K X] (Φ : X ≃ₗ[K] V)

@[expose] noncomputable def frameUnit (M : X ≃ₗ[K] X) : LinearMap.GeneralLinearGroup K V :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K V).symm (Φ.symm.trans (M.trans Φ))

theorem coe_frameUnit (M : X ≃ₗ[K] X) :
    ((frameUnit Φ M : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) =
      (Φ.symm.trans (M.trans Φ) : V →ₗ[K] V) := by
  rw [← LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap, frameUnit,
    MulEquiv.apply_symm_apply]

theorem frameUnit_apply (M : X ≃ₗ[K] X) (x : X) :
    ((frameUnit Φ M : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) (Φ x) = Φ (M x) := by
  rw [coe_frameUnit]
  simp

theorem frameUnit_mul (M N : X ≃ₗ[K] X) :
    frameUnit Φ M * frameUnit Φ N = frameUnit Φ (N.trans M) := by
  refine Units.ext (LinearMap.ext fun v => ?_)
  obtain ⟨x, rfl⟩ := Φ.surjective v
  rw [Units.val_mul, Module.End.mul_apply, frameUnit_apply, frameUnit_apply, frameUnit_apply]
  rfl

theorem frameUnit_eq_iff {M N : X ≃ₗ[K] X} : frameUnit Φ M = frameUnit Φ N ↔ M = N := by
  constructor
  · intro h
    refine LinearEquiv.ext fun x => Φ.injective ?_
    rw [← frameUnit_apply Φ M, ← frameUnit_apply Φ N, h]
  · rintro rfl
    rfl

theorem frameUnit_conj {M N N' : X ≃ₗ[K] X} (h : ∀ x, M (N x) = N' (M x)) :
    frameUnit Φ M * frameUnit Φ N * (frameUnit Φ M)⁻¹ = frameUnit Φ N' := by
  rw [frameUnit_mul, mul_inv_eq_iff_eq_mul, frameUnit_mul]
  congr 1
  exact LinearEquiv.ext h

variable {B : LinearMap.BilinForm K V}

theorem frameUnit_mem {M : X ≃ₗ[K] X} (hM : ∀ x y, B (Φ (M x)) (Φ (M y)) = B (Φ x) (Φ y)) :
    frameUnit Φ M ∈ sesqUnitaryGroup B := by
  rw [mem_sesqUnitaryGroup]
  intro u v
  obtain ⟨x, rfl⟩ := Φ.surjective u
  obtain ⟨y, rfl⟩ := Φ.surjective v
  rw [frameUnit_apply, frameUnit_apply]
  exact hM x y

end Unit

section Torus

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] {s : ℕ} {κ : Type}

@[expose] noncomputable def mulEquivL (a : L) (ha : a ≠ 0) : L ≃ₗ[K] L where
  toFun u := a * u
  invFun u := a⁻¹ * u
  map_add' u v := mul_add a u v
  map_smul' c u := by simp [Algebra.smul_def, mul_left_comm]
  left_inv u := by simp [inv_mul_cancel_left₀ ha]
  right_inv u := by simp [mul_inv_cancel_left₀ ha]

theorem mulEquivL_apply (a : L) (ha : a ≠ 0) (u : L) : mulEquivL (K := K) a ha u = a * u := rfl

variable {p : ℕ} [NeZero p] {ζ : L} (hζ : ζ ^ p = 1)

include hζ in
theorem root_pow_ne_zero (m : ℕ) : ζ ^ m ≠ 0 := by
  intro h0
  have h1 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne p)] at hζ
    exact zero_ne_one hζ
  exact pow_ne_zero m h1 h0

include hζ in
@[expose] noncomputable def torEquiv (f : Fin s → Multiplicative (ZMod p)) :
    ((Fin s → L) × (κ → K)) ≃ₗ[K] ((Fin s → L) × (κ → K)) :=
  monoEquiv 1 fun i => mulEquivL (ζ ^ (toAdd (f i)).val) (root_pow_ne_zero hζ _)

theorem torEquiv_apply (f : Fin s → Multiplicative (ZMod p)) (d : Fin s → L) (w : κ → K) :
    torEquiv (K := K) hζ f (d, w) = (fun i => ζ ^ (toAdd (f i)).val * d i, w) := rfl

variable {V : Type} [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V}
  {Φ : ((Fin s → L) × (κ → K)) ≃ₗ[K] V} {β : LinearMap.BilinForm K L}

include hζ in
theorem torEquiv_isom
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v) (f : Fin s → Multiplicative (ZMod p))
    (x y : (Fin s → L) × (κ → K)) :
    B (Φ (torEquiv hζ f x)) (Φ (torEquiv hζ f y)) = B (Φ x) (Φ y) := by
  refine monoEquiv_isom hdec 1 (fun i u v => ?_) x y
  rw [mulEquivL_apply, mulEquivL_apply]
  generalize (toAdd (f i)).val = m
  induction m generalizing u v with
  | zero => simp
  | succ m ih => rw [pow_succ, mul_assoc, mul_assoc, ih, hζβ]

@[expose] noncomputable def torHom
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v) :
    (Fin s → Multiplicative (ZMod p)) →* ↥(sesqUnitaryGroup B) where
  toFun f := ⟨frameUnit Φ (torEquiv hζ f), frameUnit_mem Φ (torEquiv_isom hζ hdec hζβ f)⟩
  map_one' := by
    apply Subtype.ext
    change frameUnit Φ (torEquiv hζ 1) = 1
    refine Units.ext (LinearMap.ext fun v => ?_)
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [frameUnit_apply, torEquiv_apply, Units.val_one, Module.End.one_apply]
    congr 2
    funext i
    simp
  map_mul' f f' := by
    apply Subtype.ext
    change frameUnit Φ (torEquiv hζ (f * f')) =
      frameUnit Φ (torEquiv hζ f) * frameUnit Φ (torEquiv hζ f')
    rw [frameUnit_mul]
    congr 1
    refine LinearEquiv.ext fun x => ?_
    obtain ⟨d, w⟩ := x
    simp only [LinearEquiv.trans_apply, torEquiv_apply]
    congr 2
    funext i
    rw [Pi.mul_apply, toAdd_mul, CoordSL.pow_val_add hζ, mul_assoc, mul_left_comm]

theorem coe_torHom
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v) (f : Fin s → Multiplicative (ZMod p)) :
    ((torHom hζ hdec hζβ f : ↥(sesqUnitaryGroup B)) : LinearMap.GeneralLinearGroup K V) =
      frameUnit Φ (torEquiv hζ f) := rfl

theorem torHom_injective
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v) (hζo : IsPrimitiveRoot ζ p) :
    Function.Injective (torHom hζ hdec hζβ) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  have h1 : frameUnit Φ (torEquiv hζ f) = frameUnit Φ (LinearEquiv.refl K _) := by
    have := congrArg Subtype.val hf
    rw [coe_torHom] at this
    rw [this]
    refine Units.ext (LinearMap.ext fun v => ?_)
    obtain ⟨x, rfl⟩ := Φ.surjective v
    rw [frameUnit_apply]
    rfl
  rw [frameUnit_eq_iff] at h1
  funext i
  have h2 := congrArg (fun x : (Fin s → L) × (κ → K) => x.1 i)
    (LinearEquiv.congr_fun h1 (fun _ => 1, 0))
  simp only [torEquiv_apply, mul_one, LinearEquiv.refl_apply] at h2
  have h3 := (hζo.pow_eq_one_iff_dvd _).mp h2
  rw [Pi.one_apply, ← ofAdd_zero, ← ofAdd_toAdd (f i)]
  congr 1
  rw [← ZMod.natCast_zmod_val (toAdd (f i)), (ZMod.natCast_eq_zero_iff _ _).mpr h3]

theorem torHom_sgn
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v) {σ : L ≃ₗ[K] L}
    (hσζ : ∀ u, σ (ζ * u) = ζ ^ (p - 1) * σ u) (hσβ : ∀ u v, β (σ u) (σ v) = β u v)
    (i : Fin s) : ∃ w : ↥(sesqUnitaryGroup B), ∀ f,
      w * torHom hζ hdec hζβ f * w⁻¹ = torHom hζ hdec hζβ (SpCoord.sgnAut i f) := by
  classical
  set T : Fin s → (L ≃ₗ[K] L) := Function.update (fun _ => LinearEquiv.refl K L) i σ with hT
  have hTβ : ∀ j u v, β (T j u) (T j v) = β u v := by
    intro j u v
    by_cases hj : j = i
    · subst hj
      rw [hT, Function.update_self]
      exact hσβ u v
    · rw [hT, Function.update_of_ne hj]
      rfl
  refine ⟨⟨frameUnit Φ (monoEquiv 1 T), frameUnit_mem Φ (monoEquiv_isom hdec 1 hTβ)⟩,
    fun f => Subtype.ext ?_⟩
  change frameUnit Φ (monoEquiv 1 T) * frameUnit Φ (torEquiv hζ f) *
      (frameUnit Φ (monoEquiv 1 T))⁻¹ = frameUnit Φ (torEquiv hζ (SpCoord.sgnAut i f))
  refine frameUnit_conj Φ fun x => ?_
  obtain ⟨d, w⟩ := x
  simp only [monoEquiv_apply, torEquiv_apply, Equiv.Perm.one_apply]
  congr 2
  funext j
  by_cases hj : j = i
  · subst hj
    rw [hT, Function.update_self, SpCoord.sgnAut_apply, Function.update_self, toAdd_inv]
    have hσpow : ∀ (m : ℕ) (u : L), σ (ζ ^ m * u) = ζ ^ ((p - 1) * m) * σ u := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        intro u
        rw [pow_succ, mul_assoc, ih, hσζ, ← mul_assoc, ← pow_add, Nat.mul_succ]
    rw [hσpow]
    congr 1
    have hpos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
    have h1 : ζ ^ ((p - 1) * (toAdd (f j)).val) * ζ ^ (toAdd (f j)).val = 1 := by
      have e : (p - 1) * (toAdd (f j)).val + (toAdd (f j)).val = p * (toAdd (f j)).val := by
        rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left _ hpos)]
      rw [← pow_add, e, pow_mul, hζ, one_pow]
    have h2 : ζ ^ (-toAdd (f j)).val * ζ ^ (toAdd (f j)).val = 1 := by
      rw [← CoordSL.pow_val_add hζ, neg_add_cancel, ZMod.val_zero, pow_zero]
    exact mul_right_cancel₀ (root_pow_ne_zero hζ _) (h1.trans h2.symm)
  · rw [hT, Function.update_of_ne hj, SpCoord.sgnAut_apply, Function.update_of_ne hj]
    rfl

theorem torHom_perm
    (hdec : ∀ d d' w w', B (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + B (Φ (0, w)) (Φ (0, w')))
    (hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v) (σ : Equiv.Perm (Fin s)) :
    ∃ w : ↥(sesqUnitaryGroup B), ∀ f,
      w * torHom hζ hdec hζβ f * w⁻¹ = torHom hζ hdec hζβ (SpCoord.permAut σ f) := by
  refine ⟨⟨frameUnit Φ (monoEquiv σ⁻¹ fun _ => LinearEquiv.refl K L),
    frameUnit_mem Φ (monoEquiv_isom hdec σ⁻¹ fun _ _ _ => rfl)⟩, fun f => Subtype.ext ?_⟩
  change frameUnit Φ (monoEquiv σ⁻¹ fun _ => LinearEquiv.refl K L) * frameUnit Φ (torEquiv hζ f) *
      (frameUnit Φ (monoEquiv σ⁻¹ fun _ => LinearEquiv.refl K L))⁻¹ =
    frameUnit Φ (torEquiv hζ (SpCoord.permAut σ f))
  refine frameUnit_conj Φ fun x => ?_
  obtain ⟨d, w⟩ := x
  simp only [monoEquiv_apply, torEquiv_apply, LinearEquiv.refl_apply, SpCoord.permAut_apply,
    Function.comp_apply]

end Torus

end SpNS

end CFSG.StandardType
