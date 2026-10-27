module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def TwoReducedOn (Γ : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) : Prop :=
  ∀ N : Subgroup (GLV V), N ≤ Γ → (∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) →
    (∀ n ∈ N, ∃ k : ℕ, ∀ u ∈ U, (n ^ 2 ^ k) u = u) → ∀ n ∈ N, ∀ u ∈ U, n u = u

@[expose] def IsDualOf (K : Subgroup (GLV V)) (I J : Submodule (ZMod 2) V) : Prop :=
  ∃ β : J →ₗ[ZMod 2] I →ₗ[ZMod 2] ZMod 2, (∀ j, (∀ i, β j i = 0) → j = 0) ∧
    (∀ i, (∀ j, β j i = 0) → i = 0) ∧
    ∀ k ∈ K, ∀ j j' : J, ∀ i i' : I,
      k (j : V) = (j' : V) → k (i : V) = (i' : V) → β j' i' = β j i

structure G108Hyp (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) : Prop
    extends G101Hyp B Γ v₁ W X X₀ where
  irreducible : IsIrr Γ ⊤
  component : IsComponentOf L Γ
  noncomm : ∃ x ∈ X, ∃ l ∈ L, x * l ≠ l * x
  three : fixedSpace X = Submodule.span (ZMod 2) {v₁} ∨ numConjugates Γ L ≤ 2
  four : ∃ S : Subgroup (GLV V), IsSylowTwoOf S (Γ ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v₁) ∧
    X ≤ S ∧ S ≤ Subgroup.normalizer (X : Set (V ≃ₗ[ZMod 2] V))

variable (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
  (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V))

@[expose] def G1003Concl : Prop :=
  (∀ U : Submodule (ZMod 2) V, U ≠ ⊥ → Invariant Γ U → TwoReducedOn Γ U) ∧ pCoreOf 2 Γ = ⊥

@[expose] def G1003Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G101Hyp B Γ v₁ W X X₀ → G1003Concl Γ

@[expose] def G1004Concl (U : Submodule (ZMod 2) V) : Prop :=
  Module.finrank (ZMod 2) V = 4 ∧ Module.finrank (ZMod 2) U = 2 ∧ Group.IsSolvable ↥Γ

@[expose] def G1004Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G101Hyp B Γ v₁ W X X₀ → ∀ (H : Subgroup (GLV V)), H ≤ Γ →
      (∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) → H ≠ ⊥ →
      ∀ U : Submodule (ZMod 2) V, U ≠ ⊥ → U ≠ ⊤ → IsIrr (H ⊔ X) U →
        (H = Γ ∨ (v₁ ∉ U ∧ commSpace X U ≠ ⊥)) → G1004Concl Γ U

@[expose] def G1005Concl : Prop :=
  IsIrr Γ ⊤ ∨ (Module.finrank (ZMod 2) V = 4 ∧ 18 ∣ Nat.card Γ)

@[expose] def G1005Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ : Subgroup (GLV V)),
    G101Hyp B Γ v₁ W X X₀ → G1005Concl Γ

@[expose] def G1007Concl : Prop :=
  fixedSpace (normalClosure Γ L) = ⊥ ∧ commSpace (normalClosure Γ L) ⊤ = ⊤ ∧
    sSup {I | IrrPlus (normalClosure Γ L) I} = ⊤ ∧
    ∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I →
      IsIrr (normalClosure Γ L) I ∧
      (∀ γ ∈ Γ, conjSub γ I = I ∨ conjSub γ I ⊓ I = ⊥) ∧ (Isotropic B I ∨ NondegOn B I) ∧
      (NondegOn B I → IsCompl I (B.orthogonal I)) ∧
      (Isotropic B I → ∃ I₂ : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I₂ ∧
        IsDualOf (normalClosure Γ L) I I₂ ∧ NondegOn B (I ⊔ I₂)) ∧
      2 < Module.finrank (ZMod 2) I

@[expose] def G1010Concl : Prop :=
  ∀ U : Submodule (ZMod 2) V, U ≠ ⊥ → Invariant (normalClosure Γ L ⊔ X) U →
    v₁ ∈ U ∧ commSpace X U ≠ ⊥

@[expose] def G1011Concl : Prop :=
  ∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I → (Invariant X I ↔ v₁ ∈ I)

@[expose] def G1012Concl : Prop :=
  ∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I → v₁ ∉ I →
    Module.finrank (ZMod 2) ↥(I ⊓ W) ≤ 1 ∧
      (I ⊓ W ≠ ⊥ → (stabilizerOf X I).relIndex X = 2)

@[expose] def G1013Concl : Prop :=
  ∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I → v₁ ∈ I →
    Isotropic B I ∨ (I = ⊤ ∧ IsIrr (normalClosure Γ L) ⊤)

@[expose] def G1014Concl : Prop :=
  ∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I → v₁ ∉ I →
    ∀ x ∈ stabilizerOf X I, x ≠ 1 →
      (∃ h ∈ normalClosure Γ L, x * h * x⁻¹ * h⁻¹ ∉ centralizerOn (normalClosure Γ L) I) →
      (I ≤ perp B v₁ ∧ ∃ c : V, I ⊓ W = Submodule.span (ZMod 2) {c} ∧ InducesTransvection x I c) ∨
      (¬ I ≤ perp B v₁ ∧ (∃ c : V, InducesTransvection x I c) ∧
        ∀ i ∈ I, x i = i ↔ i ∈ perp B v₁) ∨
      (¬ I ≤ perp B v₁ ∧ Module.finrank (ZMod 2) (commSpace (Subgroup.zpowers x) I) ≤ 2 ∧
        ∃ c : V, I ⊓ W = Submodule.span (ZMod 2) {c} ∧ InducesTransvection x (I ⊓ perp B v₁) c)

@[expose] def G1015Concl : Prop :=
  ∃ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I ∧
    ((Homogeneous (normalClosure Γ L) ∧ Invariant X I ∧ v₁ ∈ I ∧
        ∀ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J → Invariant X J → J = I) ∨
      (∃ x ∈ X, conjSub x I ≠ I ∧ IsCompl I (conjSub x I) ∧
        ¬ HIso (normalClosure Γ L) I (conjSub x I) ∧
        ∃ (i : V) (hi : i ∈ I ⊓ perp B v₁), i ≠ 0 ∧ I ⊓ W = Submodule.span (ZMod 2) {i} ∧
          v₁ = i + x i ∧
          (fixedSpace X = Submodule.span (ZMod 2) {v₁} →
            fixedSpace (stabilizerOf X I) ⊓ I = Submodule.span (ZMod 2) {i}) ∧
          (∀ y ∈ stabilizerOf X I, (∀ h ∈ normalClosure Γ L, y * h = h * y) → y = 1) ∧
          FaithfulOn (stabilizerOf X I) I ∧
          FullTransvections (stabilizerOf X I) (I ⊓ perp B v₁) i hi)) ∧
    ((Homogeneous (normalClosure Γ L) ∧ SelfDual (normalClosure Γ L) I ∧
        FaithfulOn (normalClosure Γ L) I ∧ (Isotropic B I ∨ I = ⊤)) ∨
      (¬ Homogeneous (normalClosure Γ L) ∧ ¬ SelfDual (normalClosure Γ L) I ∧
        FaithfulOn (normalClosure Γ L) I ∧ Isotropic B I ∧
        ∀ x ∈ X, conjSub x I ≠ I → IsDualOf (normalClosure Γ L) I (conjSub x I)) ∨
      (¬ Homogeneous (normalClosure Γ L) ∧ SelfDual (normalClosure Γ L) I ∧ NondegOn B I ∧
        ¬ FaithfulOn (normalClosure Γ L) I ∧ Module.finrank (ZMod 2) V = 8 ∧
        ∃ x ∈ X, conjSub x I ≠ I ∧
          normalClosure Γ L = L ⊔ L.map (MulAut.conj x).toMonoidHom ∧
          Nat.card X = 8 ∧ X = (X ⊓ normalClosure Γ L) ⊔ Subgroup.zpowers x ∧
          I = commSpace L ⊤ ∧ IsA5Module L I ∧ conjSub x I = fixedSpace L)) ∧
    (¬ AutAll (normalClosure Γ L) I ∨ Module.finrank (ZMod 2) I = 4)

@[expose] def G1016Concl : Prop :=
  ∀ a ∈ X, a ≠ 1 → Module.finrank (ZMod 2) (LinearMap.range (a.toLinearMap - LinearMap.id)) ≤ 2 →
    (∃ h ∈ normalClosure Γ L, a * h ≠ h * a) ∧
    (∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I → conjSub a I = I) ∧
    (normalClosure Γ L ≤ normalClosure Γ (Subgroup.zpowers a) ∧
      ∀ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I ↔
        IrrPlus (normalClosure Γ (Subgroup.zpowers a)) I) ∧
    (IsIrr (normalClosure Γ L) ⊤ ∨
      ∃ I₁ I₂ : Submodule (ZMod 2) V, IsCompl I₁ I₂ ∧
        Invariant (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ ∧
        Invariant (normalClosure Γ L ⊔ Subgroup.zpowers a) I₂ ∧
        (HIso (normalClosure Γ L ⊔ Subgroup.zpowers a) I₁ I₂ ∨
          (Module.finrank (ZMod 2) I₁ = 4 ∧ AutAll (normalClosure Γ L) I₁)) ∧
        (∃ c₁ : V, InducesTransvection a I₁ c₁) ∧ (∃ c₂ : V, InducesTransvection a I₂ c₂))

@[expose] def G1007Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G108Hyp B Γ v₁ W X X₀ L → G1007Concl B Γ L

@[expose] def G1010Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G108Hyp B Γ v₁ W X X₀ L → G1010Concl Γ v₁ X L

@[expose] def G1011Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G108Hyp B Γ v₁ W X X₀ L → G1011Concl Γ v₁ X L

@[expose] def G1012Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G108Hyp B Γ v₁ W X X₀ L → G1012Concl Γ v₁ W X L

@[expose] def G1013Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G108Hyp B Γ v₁ W X X₀ L → G1013Concl B Γ v₁ L

@[expose] def G1014Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G108Hyp B Γ v₁ W X X₀ L → G1014Concl B Γ v₁ W X L

@[expose] def G1015Stmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G108Hyp B Γ v₁ W X X₀ L → IsQuotientOfSQTKTauCeti ↥Γ → G1015Concl B Γ v₁ W X L

end G11

end CFSG.Quasithin
