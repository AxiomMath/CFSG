module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.StandardType

namespace ChoiceTwo

section Acts

variable {K : Type} [Field K] {n : ℕ} {X : Type} [AddCommGroup X] [Module K X]

@[expose] def ActsAs (Φ : X ≃ₗ[K] (Fin n ⊕ Fin n → K)) (Y : StatedSp n K) (M : X → X) : Prop :=
  ∀ x, spEnd Y (Φ x) = Φ (M x)

variable {Φ : X ≃ₗ[K] (Fin n ⊕ Fin n → K)}

theorem spEnd_mul_apply (Y Z : StatedSp n K) (v : Fin n ⊕ Fin n → K) :
    spEnd (Y * Z) v = spEnd Y (spEnd Z v) := by
  rw [spEnd_apply, spEnd_apply, spEnd_apply, Subgroup.coe_mul, Units.val_mul,
    Matrix.mulVec_mulVec]

theorem spEnd_one_apply (v : Fin n ⊕ Fin n → K) : spEnd (1 : StatedSp n K) v = v := by
  rw [spEnd_apply, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]

theorem eq_of_spEnd_eq' {Y Z : StatedSp n K} (h : ∀ v, spEnd Y v = spEnd Z v) : Y = Z :=
  spLin_injective (Units.ext (LinearMap.ext h))

theorem ActsAs.mul {Y Z : StatedSp n K} {M N : X → X} (hY : ActsAs Φ Y M) (hZ : ActsAs Φ Z N) :
    ActsAs Φ (Y * Z) (M ∘ N) := fun x => by
  rw [spEnd_mul_apply, hZ, hY]
  rfl

theorem ActsAs.one : ActsAs Φ (1 : StatedSp n K) id := fun _ => spEnd_one_apply _

theorem ActsAs.inv {Y : StatedSp n K} {M N : X → X} (hY : ActsAs Φ Y M)
    (hMN : ∀ x, M (N x) = x) : ActsAs Φ Y⁻¹ N := fun x => by
  have h1 : spEnd Y (Φ (N x)) = Φ x := by rw [hY, hMN]
  rw [← h1, ← spEnd_mul_apply, inv_mul_cancel, spEnd_one_apply]

theorem ActsAs.eq {Y Z : StatedSp n K} {M : X → X} (hY : ActsAs Φ Y M) (hZ : ActsAs Φ Z M) :
    Y = Z :=
  eq_of_spEnd_eq' fun v => by
    obtain ⟨x, rfl⟩ := Φ.surjective v
    rw [hY, hZ]

theorem ActsAs.congr {Y : StatedSp n K} {M N : X → X} (hY : ActsAs Φ Y M) (h : ∀ x, M x = N x) :
    ActsAs Φ Y N := fun x => by rw [hY, h]

theorem ActsAs.pow {Y : StatedSp n K} {M : X → X} (hY : ActsAs Φ Y M) (m : ℕ) :
    ActsAs Φ (Y ^ m) M^[m] := by
  induction m with
  | zero => exact ActsAs.one
  | succ m ih =>
    rw [pow_succ, Function.iterate_succ]
    exact ih.mul hY

theorem exists_actsAs (M : X ≃ₗ[K] X)
    (hM : ∀ x y, spForm n K (Φ (M x)) (Φ (M y)) = spForm n K (Φ x) (Φ y)) :
    ∃ Y : StatedSp n K, ActsAs Φ Y M := by
  have hmem := SpNS.frameUnit_mem Φ hM
  rw [← range_spLin] at hmem
  obtain ⟨Y, hY⟩ := hmem
  refine ⟨Y, fun x => ?_⟩
  change ((spLin n K Y : LinearMap.GeneralLinearGroup K _) : _ →ₗ[K] _) (Φ x) = Φ (M x)
  rw [hY, SpNS.frameUnit_apply]

theorem ActsAs.commute {Y Z : StatedSp n K} {M N : X → X} (hY : ActsAs Φ Y M)
    (hZ : ActsAs Φ Z N) (h : ∀ x, M (N x) = N (M x)) : Y * Z = Z * Y :=
  (hY.mul hZ).eq ((hZ.mul hY).congr fun x => (h x).symm)

end Acts

section Torus

variable {L : Type} [Field L] {s : ℕ}

@[expose] def torE (ζ : L) (f : Fin s → ZMod 3) (d : Fin s → L) : Fin s → L :=
  fun i => ζ ^ (f i).val * d i

theorem torE_apply (ζ : L) (f : Fin s → ZMod 3) (d : Fin s → L) (i : Fin s) :
    torE ζ f d i = ζ ^ (f i).val * d i := rfl

variable {ζ : L}

theorem torE_add (hζ : ζ ^ 3 = 1) (f f' : Fin s → ZMod 3) (d : Fin s → L) :
    torE ζ (f + f') d = torE ζ f (torE ζ f' d) := by
  funext i
  simp only [torE_apply, Pi.add_apply]
  rw [CoordSL.pow_val_add hζ, mul_assoc]

theorem torE_zero (d : Fin s → L) : torE ζ (0 : Fin s → ZMod 3) d = d := by
  funext i
  simp [torE_apply]

theorem torE_neg (hζ : ζ ^ 3 = 1) (f : Fin s → ZMod 3) (d : Fin s → L) :
    torE ζ f (torE ζ (-f) d) = d := by
  have h : f + -f = 0 := funext fun i => add_neg_cancel (f i)
  rw [← torE_add hζ, h, torE_zero]

theorem torE_neg' (hζ : ζ ^ 3 = 1) (f : Fin s → ZMod 3) (d : Fin s → L) :
    torE ζ (-f) (torE ζ f d) = d := by
  have h : -f + f = 0 := funext fun i => neg_add_cancel (f i)
  rw [← torE_add hζ, h, torE_zero]

theorem torE_injective (hζo : IsPrimitiveRoot ζ 3) {f f' : Fin s → ZMod 3}
    (h : ∀ d, torE ζ f d = torE ζ f' d) : f = f' := by
  funext i
  have h1 := congrFun (h fun _ => 1) i
  simp only [torE_apply, mul_one] at h1
  have h2 := hζo.pow_inj (ZMod.val_lt (f i)) (ZMod.val_lt (f' i)) h1
  rw [← ZMod.natCast_zmod_val (f i), ← ZMod.natCast_zmod_val (f' i), h2]

@[expose] noncomputable def torLE (K : Type) [Field K] [Algebra K L] (hζ : ζ ^ 3 = 1)
    (f : Fin s → ZMod 3) : (Fin s → L) ≃ₗ[K] (Fin s → L) where
  toFun := torE ζ f
  invFun := torE ζ (-f)
  map_add' d d' := funext fun i => mul_add _ _ _
  map_smul' c d := funext fun i => by
    change ζ ^ (f i).val * (c • d i) = c • (ζ ^ (f i).val * d i)
    rw [mul_smul_comm]
  left_inv d := torE_neg' hζ f d
  right_inv d := torE_neg hζ f d

theorem torLE_apply (K : Type) [Field K] [Algebra K L] (hζ : ζ ^ 3 = 1) (f : Fin s → ZMod 3)
    (d : Fin s → L) : torLE K hζ f d = torE ζ f d := rfl

end Torus

section Cyc

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
  (B₀ : LinearMap.BilinForm K W) (u v : W)

@[expose] noncomputable def cyc3 : W →ₗ[K] W :=
  LinearMap.id + (B₀.flip v + B₀ u).smulRight u + (B₀.flip v).smulRight v

theorem cyc3_apply (w : W) : cyc3 B₀ u v w = w + (B₀ w v + B₀ u w) • u + B₀ w v • v := by
  simp [cyc3, LinearMap.smulRight_apply]

variable {B₀ u v}

theorem cyc3_isom (hB : B₀.IsAlt) (huv : B₀ u v = 1) (w w' : W) :
    B₀ (cyc3 B₀ u v w) (cyc3 B₀ u v w') = B₀ w w' := by
  have h1 : B₀ w u = -B₀ u w := (hB.neg_eq u w).symm
  have h4 : B₀ v w' = -B₀ w' v := (hB.neg_eq w' v).symm
  have h5 : B₀ v u = -1 := by rw [← huv]; exact (hB.neg_eq u v).symm
  have h2 : B₀ u u = 0 := hB u
  have h6 : B₀ v v = 0 := hB v
  have h3 := huv
  rw [cyc3_apply, cyc3_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  linear_combination (B₀ w' v + B₀ u w') * h1 + (B₀ w v + B₀ u w) * (B₀ w' v + B₀ u w') * h2 +
    (B₀ w v + B₀ u w) * B₀ w' v * h3 + B₀ w v * h4 + B₀ w v * (B₀ w' v + B₀ u w') * h5 +
    B₀ w v * B₀ w' v * h6

theorem cyc3_v (hB : B₀.IsAlt) (huv : B₀ u v = 1) : cyc3 B₀ u v v = u + v := by
  rw [cyc3_apply, huv, hB v, zero_add, zero_smul, add_zero, one_smul, add_comm]

variable [CharP K 2]

omit [Module K W] in
theorem add_self_eq_zero_of_charTwo [Module K W] (w : W) : w + w = 0 := by
  rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]

theorem cyc3_u (hB : B₀.IsAlt) (huv : B₀ u v = 1) : cyc3 B₀ u v u = v := by
  rw [cyc3_apply, huv, hB u, add_zero, one_smul, one_smul, add_self_eq_zero_of_charTwo (K := K),
    zero_add]

theorem cyc3_cube (hB : B₀.IsAlt) (huv : B₀ u v = 1) (w : W) :
    cyc3 B₀ u v (cyc3 B₀ u v (cyc3 B₀ u v w)) = w := by
  set c₁ := B₀ w v + B₀ u w
  set c₂ := B₀ w v
  have e1 : cyc3 B₀ u v w = w + c₁ • u + c₂ • v := cyc3_apply B₀ u v w
  have e2 : cyc3 B₀ u v (cyc3 B₀ u v w) = w + (c₁ + c₂) • u + (c₁ + c₂ + c₂) • v := by
    rw [e1, map_add, map_add, map_smul, map_smul, cyc3_u hB huv, cyc3_v hB huv, e1]
    module
  rw [e2, map_add, map_add, map_smul, map_smul, cyc3_u hB huv, cyc3_v hB huv, e1]
  have h1 : c₁ + (c₁ + c₂ + c₂) = 0 := by
    rw [show c₁ + (c₁ + c₂ + c₂) = (c₁ + c₁) + (c₂ + c₂) by ring]
    simp [CharTwo.add_self_eq_zero]
  have h2 : c₂ + (c₁ + c₂) + (c₁ + c₂ + c₂) = 0 := by
    rw [show c₂ + (c₁ + c₂) + (c₁ + c₂ + c₂) = (c₁ + c₁) + ((c₂ + c₂) + (c₂ + c₂)) by ring]
    simp [CharTwo.add_self_eq_zero]
  calc w + c₁ • u + c₂ • v + (c₁ + c₂) • v + (c₁ + c₂ + c₂) • (u + v) =
      w + (c₁ + (c₁ + c₂ + c₂)) • u + (c₂ + (c₁ + c₂) + (c₁ + c₂ + c₂)) • v := by module
    _ = w := by rw [h1, h2, zero_smul, zero_smul, add_zero, add_zero]

theorem cyc3_ne (hB : B₀.IsAlt) (huv : B₀ u v = 1) : cyc3 B₀ u v u ≠ u := by
  rw [cyc3_u hB huv]
  intro h
  rw [h, hB u] at huv
  exact zero_ne_one huv

end Cyc

section Frame

structure SpFrame (K : Type) [Field K] (n : ℕ) {L : Type} [Field L] [Algebra K L] (ζ : L)
    (E : Subgroup (StatedSp n K)) where
  s : ℕ
  Φ : (Fin s → L) ≃ₗ[K] (Fin n ⊕ Fin n → K)
  β : LinearMap.BilinForm K L
  σ : L ≃ₗ[K] L
  form : ∀ d d', spForm n K (Φ d) (Φ d') = ∑ i, β (d i) (d' i)
  ζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v
  σζ : ∀ u, σ (ζ * u) = ζ ^ 2 * σ u
  σσ : ∀ u, σ (σ u) = u
  σβ : ∀ u v, β (σ u) (σ v) = β u v
  tor : (Fin s → ZMod 3) → StatedSp n K
  tor_acts : ∀ f, ActsAs Φ (tor f) (torE ζ f)
  tor_mem : ∀ f, tor f ∈ E
  mem_tor : ∀ Y ∈ E, ∃ f, tor f = Y

variable {K : Type} [Field K] {n : ℕ}

theorem spEnd_mul (Y Z : StatedSp n K) : spEnd (Y * Z) = spEnd Y * spEnd Z :=
  LinearMap.ext fun v => (spEnd_mul_apply Y Z v).trans (Module.End.mul_apply _ _ _).symm

theorem spEnd_one : spEnd (1 : StatedSp n K) = 1 := LinearMap.ext fun v => spEnd_one_apply v

theorem spEnd_pow (Y : StatedSp n K) (m : ℕ) : spEnd (Y ^ m) = spEnd Y ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, spEnd_one]
  | succ m ih => rw [pow_succ, pow_succ, spEnd_mul, ih]

theorem bilin_pow_mul {L : Type} [Field L] [Algebra K L] {β : LinearMap.BilinForm K L} {ζ : L}
    (hζβ : ∀ u v, β (ζ * u) (ζ * v) = β u v) (m : ℕ) (u v : L) :
    β (ζ ^ m * u) (ζ ^ m * v) = β u v := by
  induction m generalizing u v with
  | zero => simp
  | succ m ih => rw [pow_succ', mul_assoc, mul_assoc, hζβ, ih]

end Frame

end ChoiceTwo

end CFSG.StandardType
