module

public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Open.QuasithinDefs
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix TensorProduct

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def endCommutant (H : Subgroup (GLV V)) :
    Subalgebra (ZMod 2) (Module.End (ZMod 2) V) :=
  Subalgebra.centralizer (ZMod 2) {f | ∃ h ∈ H, f = (h : V →ₗ[ZMod 2] V)}

@[expose] def EndIsField (H : Subgroup (GLV V)) (e : ℕ) : Prop :=
  Nonempty (↥(endCommutant H) ≃ₐ[ZMod 2] GaloisField 2 e)

@[expose] def QuasiEquivalent (L L₂ : Subgroup (GLV V)) : Prop :=
  ∃ φ : ↥L ≃* ↥L₂,
    (∃ ψ : V ≃ₗ[ZMod 2] V, ∀ (l : ↥L) (v : V),
      ψ ((l : GLV V) v) = ((φ l : ↥L₂) : GLV V) (ψ v)) ∨
    (∃ ψ : V ≃ₗ[ZMod 2] (V →ₗ[ZMod 2] ZMod 2), ∀ (l : ↥L) (v w : V),
      ψ ((l : GLV V) v) (((φ l : ↥L₂) : GLV V) w) = ψ v w)

@[expose] def IsNaturalMatrixModule {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Algebra (ZMod 2) K] (H : Subgroup (GLV V)) (Γ₀ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    Prop :=
  ∃ (φ : ↥H ≃* ↥Γ₀) (ψ : V ≃ₗ[ZMod 2] (ι → K)), ∀ (h : ↥H) (v : V),
    ψ ((h : GLV V) v) = ((φ h : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ ψ v

@[expose] def IsPermCoreModule {n : ℕ} (H : Subgroup (GLV V)) (G₀ : Subgroup (Equiv.Perm (Fin n))) :
    Prop :=
  ∃ (φ : ↥H ≃* ↥G₀) (β : ↥(permCore n) →ₗ[ZMod 2] V),
    Function.Surjective β ∧
    (∀ u : ↥(permCore n), β u = 0 ↔ (u = 0 ∨ (Even n ∧ ∀ i, (u : Fin n → ZMod 2) i = 1))) ∧
    ∀ (γ : ↥H) (u u' : ↥(permCore n)),
      (u' : Fin n → ZMod 2) = permAct ((φ γ : ↥G₀) : Equiv.Perm (Fin n)) (u : Fin n → ZMod 2) →
        β u' = (γ : GLV V) (β u)

@[expose] def IsG2NaturalModule {K : Type} [Field K] [Algebra (ZMod 2) K] (H : Subgroup (GLV V))
    (G₀ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K)) : Prop :=
  ∃ (φ : ↥H ≃* ↥G₀) (π : quasithinZorn K →ₗ[ZMod 2] V),
    (∀ v : V, ∃ x : quasithinZorn K, x.1 + x.2.2.2 = 0 ∧ π x = v) ∧
    (∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 → (π x = 0 ↔ ∃ c : K, x = (c, 0, 0, c))) ∧
    ∀ (h : ↥H) (x : quasithinZorn K), x.1 + x.2.2.2 = 0 →
      π (((φ h : ↥G₀) : quasithinZorn K ≃ₗ[K] quasithinZorn K) x) = (h : GLV V) (π x)

@[expose] def IsL3L3TensorModule (Γ : Subgroup (GLV V)) : Prop :=
  ∃ (φ : ↥Γ ≃* (↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2))))
    (ψ : V ≃ₗ[ZMod 2] Matrix (Fin 3) (Fin 3) (ZMod 2)), ∀ (γ : ↥Γ) (v : V),
      ψ ((γ : GLV V) v) =
        (((φ γ).1 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          ψ v * (((φ γ).2 : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
            Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ

@[expose] noncomputable def tensorN3Act (g : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) :
    ((Fin 2 → GaloisField 2 3) ⊗[GaloisField 2 3]
      ((Fin 2 → GaloisField 2 3) ⊗[GaloisField 2 3] (Fin 2 → GaloisField 2 3))) →ₗ[GaloisField 2 3]
    ((Fin 2 → GaloisField 2 3) ⊗[GaloisField 2 3]
      ((Fin 2 → GaloisField 2 3) ⊗[GaloisField 2 3] (Fin 2 → GaloisField 2 3))) :=
  TensorProduct.map (Matrix.toLin' g)
    (TensorProduct.map (Matrix.toLin' (g.map fun x => x ^ 2)) (Matrix.toLin' (g.map fun x => x ^ 4)))

@[expose] def IsL28TwistedTensorModule (H : Subgroup (GLV V)) : Prop :=
  ∃ (φ : ↥H ≃* ↥(StatedSL 2 (GaloisField 2 3)))
    (ψ : (GaloisField 2 3 ⊗[ZMod 2] V) ≃ₗ[GaloisField 2 3]
      ((Fin 2 → GaloisField 2 3) ⊗[GaloisField 2 3]
        ((Fin 2 → GaloisField 2 3) ⊗[GaloisField 2 3] (Fin 2 → GaloisField 2 3)))),
    ∀ (h : ↥H) (x : GaloisField 2 3 ⊗[ZMod 2] V),
      ψ (LinearMap.baseChange (GaloisField 2 3) ((h : GLV V) : V →ₗ[ZMod 2] V) x) =
        tensorN3Act (((φ h : ↥(StatedSL 2 (GaloisField 2 3))) :
          Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 3)) :
            Matrix (Fin 2) (Fin 2) (GaloisField 2 3)) (ψ x)

@[expose] def IsHermitianTensorModule (H : Subgroup (GLV V)) (n : ℕ) : Prop :=
  ∃ (π : ↥(StatedSL 3 (GaloisField 2 (2 * n))) →* ↥H)
    (ψ : V →ₗ[ZMod 2] Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))),
    Function.Surjective π ∧ Function.Injective ψ ∧
    (∀ X : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)),
      (∃ v, ψ v = X) ↔ ∀ i j, X i j = X j i ^ 2 ^ n) ∧
    ∀ (g : ↥(StatedSL 3 (GaloisField 2 (2 * n)))) (v : V),
      ψ ((π g : GLV V) v) =
        (((g : Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 (2 * n))) :
          Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)))) * ψ v *
        ((((g : Matrix.GeneralLinearGroup (Fin 3) (GaloisField 2 (2 * n))) :
          Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n)))).map fun x => x ^ 2 ^ n)ᵀ

@[expose] def IsPlusQuadForm (q : V → ZMod 2) : Prop :=
  ∃ B : LinearMap.BilinForm (ZMod 2) V,
    (∀ v, (∀ w, B v w = 0) → v = 0) ∧ (∀ v w, q (v + w) = q v + q w + B v w) ∧
    (∀ (c : ZMod 2) v, q (c • v) = c * c * q v) ∧
    ∃ S : Submodule (ZMod 2) V, 2 * Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) V ∧
      ∀ s ∈ S, q s = 0

@[expose] def IsGammaL24 (Γ : Subgroup (GLV V)) : Prop :=
  ∃ B : Subgroup (GLV V), Nat.card B = 3 ∧ (∀ b ∈ B, b ≠ 1 → ∀ v, b v = v → v = 0) ∧
    Γ = Subgroup.normalizer (B : Set (GLV V))

end G11

end CFSG.Quasithin
