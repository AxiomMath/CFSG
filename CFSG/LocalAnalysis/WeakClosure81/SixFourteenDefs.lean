module

public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open scoped TensorProduct

section Conclusions

variable (W : Type) [CommGroup W]

@[expose] def IsNatGL4 (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  ∃ (φ : ↥H ≃* Matrix.GeneralLinearGroup (Fin n) (GaloisField 2 2))
    (ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)),
    ∀ (a : ↥H) (w : W), ψ ((a : MulAut W) w) =
      Multiplicative.ofAdd
        ((φ a : Matrix (Fin n) (Fin n) (GaloisField 2 2)).mulVec (Multiplicative.toAdd (ψ w)))

@[expose] def IsNatSL4 (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  ∃ (φ : ↥H ≃* Matrix.SpecialLinearGroup (Fin n) (GaloisField 2 2))
    (ψ : W ≃* Multiplicative (Fin n → GaloisField 2 2)),
    ∀ (a : ↥H) (w : W), ψ ((a : MulAut W) w) =
      Multiplicative.ofAdd
        ((φ a : Matrix (Fin n) (Fin n) (GaloisField 2 2)).mulVec (Multiplicative.toAdd (ψ w)))

@[expose] def IsTensorS3L2 (G : Subgroup (MulAut W)) (m : ℕ) : Prop :=
  ∃ (φ : ↥G ≃* (Equiv.Perm (Fin 3) × Matrix.GeneralLinearGroup (Fin m) (ZMod 2)))
    (ψ : W ≃* Multiplicative (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2))),
    ∀ (γ : ↥G) (a a' : ↥(CFSG.Quasithin.permCore 3)) (c c' : Fin m → ZMod 2),
      (a' : Fin 3 → ZMod 2) = CFSG.Quasithin.permAct (φ γ).1 (a : Fin 3 → ZMod 2) →
      c' = ((φ γ).2 : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec c →
        ψ ((γ : MulAut W) (ψ.symm (Multiplicative.ofAdd (a ⊗ₜ[ZMod 2] c)))) =
          Multiplicative.ofAdd (a' ⊗ₜ[ZMod 2] c')

@[expose] def IsS6Cover (G X : Subgroup (MulAut W)) : Prop :=
  ∃ φ : ↥G →* Equiv.Perm (Fin 6), Function.Surjective φ ∧ φ.ker = X.subgroupOf G

end Conclusions

section Conclusions139

variable (W : Type) [CommGroup W]

@[expose] def Concl139Printed (G X : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  IsNatGL4 W (G ⊓ Subgroup.centralizer (X : Set (MulAut W))) n ∨ IsTensorS3L2 W G n ∨
    (IsS6Cover W G X ∧ n = 3)

@[expose] def Concl139 (G X : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  Concl139Printed W G X n ∨ IsNatSL4 W (G ⊓ Subgroup.centralizer (X : Set (MulAut W))) n

@[expose] def Concl614Printed (G X : Subgroup (MulAut W)) : Prop :=
  (∃ m : ℕ, IsTensorS3L2 W G m) ∨
    (∃ m : ℕ, IsNatGL4 W (G ⊓ Subgroup.centralizer (X : Set (MulAut W))) m) ∨
    (IsS6Cover W G X ∧ Nat.card W = 2 ^ 6)

@[expose] def Concl614 (G X : Subgroup (MulAut W)) : Prop :=
  Concl614Printed W G X ∨ ∃ m : ℕ, IsNatSL4 W (G ⊓ Subgroup.centralizer (X : Set (MulAut W))) m

end Conclusions139

@[expose] def Hyp139 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
  ∀ (G X D : Subgroup (MulAut W)) (s : MulAut W) (Y : Subgroup W) (n : ℕ),
    CFSG.Open.IsKGroup ↥G → pCoreOf 2 G = ⊥ →
    (∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤) →
    (∃ t ∈ G, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ 3) →
    X ≤ G → (∀ g ∈ G, ∀ x ∈ X, g * x * g⁻¹ ∈ X) → Nat.card X = 3 →
    s ∈ G → orderOf s = 2 → s ∉ Subgroup.centralizer (X : Set (MulAut W)) →
    (∀ x ∈ X, ∀ y ∈ Y, x y ∈ Y) → rkIdx Y = 2 → Nat.card W = 4 ^ n →
    D ≤ G → (∀ d ∈ D, ∀ x ∈ X, d * x = x * d) → (∀ d ∈ D, d * s = s * d) →
    IsElemAbelian2 D → Nat.card D = 2 ^ (n - 1) → Y ≤ fixV D →
      Concl139 W G X n

theorem concl139_of_concl139Printed {W : Type} [CommGroup W] {G X : Subgroup (MulAut W)}
    {n : ℕ} (h : Concl139Printed W G X n) : Concl139 W G X n :=
  Or.inl h

section Orbit

variable {W : Type} [CommGroup W]

@[expose] def orbitClosure (x : MulAut W) (A : Subgroup W) : Subgroup W :=
  ⨆ i : ℕ, A.map ((x ^ i : MulAut W) : W →* W)

end Orbit

end CFSG.LocalAnalysis.WeakClosure81
