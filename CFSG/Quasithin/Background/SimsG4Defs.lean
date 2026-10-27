module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.SymplecticGroup
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.SimsG4
section Sp

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def spGroup (B : LinearMap.BilinForm F V) : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | ∀ x y, B (g x) (g y) = B x y}
  mul_mem' := fun {g h} hg hh x y => by
    change B (g (h x)) (g (h y)) = B x y
    rw [hg, hh]
  one_mem' := fun x y => rfl
  inv_mem' := fun {g} hg x y => by
    have := hg (g⁻¹ x) (g⁻¹ y)
    simpa using this.symm

@[expose] def IsSympBasis (B : LinearMap.BilinForm F V) (b : Module.Basis (Fin 4) F V) : Prop :=
  ∀ i j : Fin 4, B (b i) (b j) = if i.val + j.val = 3 then 1 else 0

@[expose] def subfieldSpOf (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F) :
    Set (V ≃ₗ[F] V) :=
  {g | ∀ i j, LinearMap.toMatrix b b (g : V →ₗ[F] V) i j ∈ F₀}

@[expose] def IsTransv (g : V ≃ₗ[F] V) : Prop :=
  Module.finrank F (LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)) = 1 ∧
    ((g : V →ₗ[F] V) - LinearMap.id) ∘ₗ ((g : V →ₗ[F] V) - LinearMap.id) = 0

@[expose] def commSpace (g : V ≃ₗ[F] V) : Submodule F V :=
  LinearMap.range ((g : V →ₗ[F] V) - LinearMap.id)

@[expose] def IsMaximalSymplecticParabolic (B : LinearMap.BilinForm F V)
    (Qhat : Subgroup (V ≃ₗ[F] V)) : Prop :=
  ∃ isotropicSpace : Submodule F V,
    (Module.finrank F isotropicSpace = 1 ∨ Module.finrank F isotropicSpace = 2) ∧
    (∀ vector ∈ isotropicSpace, ∀ other ∈ isotropicSpace, B vector other = 0) ∧
    ∀ automorphism : V ≃ₗ[F] V,
      automorphism ∈ Qhat ↔ automorphism ∈ spGroup B ∧
        isotropicSpace.map (automorphism : V →ₗ[F] V) = isotropicSpace

@[expose] def twoPrimeResidual (H : Type*) [Group H] : Subgroup H :=
  sInf {N : Subgroup H | N.Normal ∧ Odd N.index}

@[expose] def twoPrimeResidualOf {A : Type*} [Group A] (H : Subgroup A) : Subgroup A :=
  (twoPrimeResidual ↥H).map H.subtype

@[expose] def transvSet (G₀ : Subgroup (V ≃ₗ[F] V)) : Set (V ≃ₗ[F] V) :=
  {d | d ∈ G₀ ∧ IsTransv d}

@[expose] def transvGen (G₀ : Subgroup (V ≃ₗ[F] V)) : Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure (transvSet G₀)

@[expose] def transvFix (G₀ : Subgroup (V ≃ₗ[F] V)) (X : Submodule F V) :
    Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure {d | d ∈ transvSet G₀ ∧ ∀ x ∈ X, d x = x}

@[expose] def IsIrredOnV (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop :=
  ∀ W : Submodule F V, (∀ g ∈ G₀, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def IsImprimitiveOnV (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop :=
  ∃ (r : ℕ) (W : Fin r → Submodule F V), 1 < r ∧ (∀ i, W i ≠ ⊥) ∧ iSupIndep W ∧
    (⨆ i, W i) = ⊤ ∧ ∀ g ∈ G₀, ∀ i, ∃ j, (W i).map (g : V →ₗ[F] V) = W j

@[expose] def rootGroupHat (B : LinearMap.BilinForm F V) (d : V ≃ₗ[F] V) :
    Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure {g | g ∈ spGroup B ∧ IsTransv g ∧ commSpace g = commSpace d}

@[expose] def xHat (B : LinearMap.BilinForm F V) (d : V ≃ₗ[F] V) : Subgroup (V ≃ₗ[F] V) :=
  Subgroup.closure {e | e ∈ spGroup B ∧ IsTransv e ∧ e * d = d * e}

@[expose] def advSet (G₀ : Subgroup (V ≃ₗ[F] V)) (d : V ≃ₗ[F] V) : Set (V ≃ₗ[F] V) :=
  {e | e ∈ transvSet G₀ ∧ e * d ≠ d * e}

@[expose] def dSet (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V))
    (d : V ≃ₗ[F] V) : Set (V ≃ₗ[F] V) :=
  {e | e ∈ transvSet G₀ ∧ e * d = d * e ∧ e ∉ rootGroupHat B d}

@[expose] def advGraph (G₀ : Subgroup (V ≃ₗ[F] V)) : SimpleGraph ↥(transvSet G₀) :=
  SimpleGraph.fromRel fun a b => (a : V ≃ₗ[F] V) * b ≠ b * a

@[expose] def invSet (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Set (V ≃ₗ[F] V) :=
  {i | i ∈ transvGen G₀ ∧ i ≠ 1 ∧ i * i = 1 ∧ ∃ a ∈ transvSet G₀, ∃ b ∈ dSet B G₀ a, i = a * b}

@[expose] def IsNondegLine (B : LinearMap.BilinForm F V) (W : Submodule F V) : Prop :=
  Module.finrank F W = 2 ∧ ∀ w ∈ W, (∀ w' ∈ W, B w w' = 0) → w = 0

@[expose] def IsTotSingLine (B : LinearMap.BilinForm F V) (W : Submodule F V) : Prop :=
  Module.finrank F W = 2 ∧ ∀ w ∈ W, ∀ w' ∈ W, B w w' = 0

end Sp

section Orth

variable (K : Type) [Field K]

@[expose] def isometryGroup (q : (Fin 4 → K) → K) : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) where
  carrier := {M | ∀ v, q ((M : Matrix (Fin 4) (Fin 4) K).mulVec v) = q v}
  mul_mem' := fun {M N} hM hN v => by
    have h1 := hM ((N : Matrix (Fin 4) (Fin 4) K).mulVec v)
    have h2 := hN v
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec] at h1 ⊢
    rw [h1, h2]
  one_mem' := fun v => by simp
  inv_mem' := fun {M} hM v => by
    have h := hM (((M⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec v)
    rw [Matrix.mulVec_mulVec] at h
    have h2 : ((M : Matrix (Fin 4) (Fin 4) K) *
        ((M⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [h2, Matrix.one_mulVec] at h
    exact h.symm

@[expose] def qPlus (v : Fin 4 → K) : K := v 0 * v 1 + v 2 * v 3

@[expose] def qMinus (c : K) (v : Fin 4 → K) : K :=
  v 0 * v 1 + v 2 ^ 2 + v 2 * v 3 + c * v 3 ^ 2

@[expose] def IsO4Type (k : ℕ) (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* isometryGroup (GaloisField 2 k) (qPlus (GaloisField 2 k))) ∨
    ∃ c : GaloisField 2 k, (¬ ∃ x : GaloisField 2 k, x ^ 2 + x + c = 0) ∧
      Nonempty (X ≃* isometryGroup (GaloisField 2 k) (qMinus (GaloisField 2 k) c))

@[expose] def orthAct {F : Type} [Field F] (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Fin 3 → F) : Fin 3 → F :=
  let M : Matrix (Fin 2) (Fin 2) F := !![v 0, v 1; v 1, v 2]
  let N : Matrix (Fin 2) (Fin 2) F :=
    (g : Matrix (Fin 2) (Fin 2) F) * M * (g : Matrix (Fin 2) (Fin 2) F).transpose
  ![N 0 0, N 0 1, N 1 1]

end Orth

section Cases

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

@[expose] def fStarOf {A : Type*} [Group A] (H : Subgroup A) : Subgroup A :=
  (CFSG.generalizedFitting ↥H).map H.subtype

@[expose] def G41Factor (n : ℕ) (X : Subgroup (V ≃ₗ[F] V)) : Prop :=
  (∃ k : ℕ, k ∣ n ∧ Nonempty (↥X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) ∨
    ∃ m : ℕ, (m ∣ 2 ^ n + 1 ∨ m ∣ 2 ^ n - 1) ∧ Nonempty (↥X ≃* DihedralGroup m)

@[expose] def G41Case1 (n : ℕ) (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Prop :=
  transvGen G₀ = G₀ ∧
    ∃ (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F) (k : ℕ),
      IsSympBasis B b ∧ 0 < k ∧ k ∣ n ∧ Nat.card F₀ = 2 ^ k ∧
      (∀ g : V ≃ₗ[F] V, g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀) ∧
      Nonempty (↥G₀ ≃* ↥(Matrix.symplecticGroup (Fin 2) (GaloisField 2 k)))

@[expose] def G41Case2 (n : ℕ) (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Prop :=
  transvGen G₀ = G₀ ∧
    ∃ (Q : QuadraticForm F V) (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F) (k : ℕ),
      (∀ x y, QuadraticMap.polar Q x y = B x y) ∧ IsSympBasis B b ∧
      0 < k ∧ k ∣ n ∧ Nat.card F₀ = 2 ^ k ∧
      (∀ g : V ≃ₗ[F] V,
        g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀ ∧ ∀ x, Q (g x) = Q x) ∧
      IsO4Type k ↥G₀

@[expose] def G41Case2AtExponent (n k : ℕ) (B : LinearMap.BilinForm F V)
    (G₀ : Subgroup (V ≃ₗ[F] V)) : Prop :=
  transvGen G₀ = G₀ ∧
    ∃ (Q : QuadraticForm F V) (b : Module.Basis (Fin 4) F V) (F₀ : Subfield F),
      (∀ x y, QuadraticMap.polar Q x y = B x y) ∧ IsSympBasis B b ∧
      0 < k ∧ k ∣ n ∧ Nat.card F₀ = 2 ^ k ∧
      (∀ g : V ≃ₗ[F] V,
        g ∈ G₀ ↔ g ∈ spGroup B ∧ g ∈ subfieldSpOf b F₀ ∧ ∀ x, Q (g x) = Q x) ∧
      IsO4Type k ↥G₀

@[expose] def G41Case3 (n : ℕ) (B : LinearMap.BilinForm F V) (G₀ : Subgroup (V ≃ₗ[F] V)) :
    Prop :=
  ∃ V₁ V₂ : Submodule F V, IsNondegLine B V₁ ∧ V₂ = LinearMap.BilinForm.orthogonal B V₁ ∧
    IsCompl V₁ V₂ ∧
    (∀ g ∈ G₀, (V₁.map (g : V →ₗ[F] V) = V₁ ∧ V₂.map (g : V →ₗ[F] V) = V₂) ∨
      (V₁.map (g : V →ₗ[F] V) = V₂ ∧ V₂.map (g : V →ₗ[F] V) = V₁)) ∧
    (∃ t ∈ G₀, t * t = 1 ∧ V₁.map (t : V →ₗ[F] V) = V₂ ∧
      G₀ = transvGen G₀ ⊔ Subgroup.zpowers t) ∧
    (transvGen G₀ = transvFix G₀ V₂ ⊔ transvFix G₀ V₁ ∧
      transvFix G₀ V₂ ⊓ transvFix G₀ V₁ = ⊥ ∧
      ∀ a ∈ transvFix G₀ V₂, ∀ b ∈ transvFix G₀ V₁, a * b = b * a) ∧
    G41Factor n (transvFix G₀ V₂) ∧ G41Factor n (transvFix G₀ V₁)

end Cases

end CFSG.Quasithin.SimsG4
