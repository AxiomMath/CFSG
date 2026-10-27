module

public import CFSG.Quasithin.Background.G11Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

@[expose] def G1015One_i (_B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (_W : Submodule (ZMod 2) V) (X L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  Homogeneous (normalClosure Γ L) ∧ Invariant X I ∧ v₁ ∈ I ∧
    ∀ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J → Invariant X J → J = I

@[expose] def G1015One_ii (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ∃ x ∈ X, conjSub x I ≠ I ∧ IsCompl I (conjSub x I) ∧
    ¬ HIso (normalClosure Γ L) I (conjSub x I) ∧
    ∃ (i : V) (hi : i ∈ I ⊓ perp B v₁), i ≠ 0 ∧ I ⊓ W = Submodule.span (ZMod 2) {i} ∧
      v₁ = i + x i ∧
      (fixedSpace X = Submodule.span (ZMod 2) {v₁} →
        fixedSpace (stabilizerOf X I) ⊓ I = Submodule.span (ZMod 2) {i}) ∧
      (∀ y ∈ stabilizerOf X I, (∀ h ∈ normalClosure Γ L, y * h = h * y) → y = 1) ∧
      FaithfulOn (stabilizerOf X I) I ∧
      FullTransvections (stabilizerOf X I) (I ⊓ perp B v₁) i hi

@[expose] def G1015Two_I (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (_v₁ : V)
    (_W : Submodule (ZMod 2) V) (_X L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  Homogeneous (normalClosure Γ L) ∧ SelfDual (normalClosure Γ L) I ∧
    FaithfulOn (normalClosure Γ L) I ∧ (Isotropic B I ∨ I = ⊤)

@[expose] def G1015Two_II (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (_v₁ : V)
    (_W : Submodule (ZMod 2) V) (X L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ¬ Homogeneous (normalClosure Γ L) ∧ ¬ SelfDual (normalClosure Γ L) I ∧
    FaithfulOn (normalClosure Γ L) I ∧ Isotropic B I ∧
    ∀ x ∈ X, conjSub x I ≠ I → IsDualOf (normalClosure Γ L) I (conjSub x I)

@[expose] def G1015Two_III (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (_v₁ : V)
    (_W : Submodule (ZMod 2) V) (X L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ¬ Homogeneous (normalClosure Γ L) ∧ SelfDual (normalClosure Γ L) I ∧ NondegOn B I ∧
    ¬ FaithfulOn (normalClosure Γ L) I ∧ Module.finrank (ZMod 2) V = 8 ∧
    ∃ x ∈ X, conjSub x I ≠ I ∧
      normalClosure Γ L = L ⊔ L.map (MulAut.conj x).toMonoidHom ∧
      Nat.card X = 8 ∧ X = (X ⊓ normalClosure Γ L) ⊔ Subgroup.zpowers x ∧
      I = commSpace L ⊤ ∧ IsA5Module L I ∧ conjSub x I = fixedSpace L

@[expose] def G1015Three (Γ : Subgroup (GLV V)) (L : Subgroup (GLV V))
    (I : Submodule (ZMod 2) V) : Prop :=
  ¬ AutAll (normalClosure Γ L) I ∨ Module.finrank (ZMod 2) I = 4

omit [Finite V] in
theorem G1015Concl_iff (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X L : Subgroup (GLV V)) : G1015Concl B Γ v₁ W X L ↔
    ∃ I : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) I ∧
      (G1015One_i B Γ v₁ W X L I ∨ G1015One_ii B Γ v₁ W X L I) ∧
      (G1015Two_I B Γ v₁ W X L I ∨ G1015Two_II B Γ v₁ W X L I ∨ G1015Two_III B Γ v₁ W X L I) ∧
      G1015Three Γ L I := Iff.rfl

@[expose] def G116IIStmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G108Hyp B Γ v₁ W X X₀ L → numConjugates Γ L ≤ 2 → IsQuotientOfSQTKTauCeti ↥Γ →
      ∀ I : Submodule (ZMod 2) V,
      IrrPlus (normalClosure Γ L) I → G1015One_ii B Γ v₁ W X L I →
        G1015Two_II B Γ v₁ W X L I → G1015Three Γ L I →
          G112Concl8 B Γ X ∨ G112Concl8S8 B Γ X

@[expose] def G116IIIStmt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)),
    G108Hyp B Γ v₁ W X X₀ L → IsQuotientOfSQTKTauCeti ↥Γ → ∀ I : Submodule (ZMod 2) V,
      IrrPlus (normalClosure Γ L) I → G1015One_ii B Γ v₁ W X L I →
        G1015Two_III B Γ v₁ W X L I → G1015Three Γ L I → G112Concl12 Γ X

end G11

end CFSG.Quasithin
