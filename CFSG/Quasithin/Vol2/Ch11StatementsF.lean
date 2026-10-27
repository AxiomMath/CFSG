module

public import CFSG.Quasithin.Vol2.Ch11StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

section Defs

variable {G : Type} [Group G]

abbrev fsmul {F : Type} [Field F] {P : Subgroup G} [IsMulCommutative ↥P]
    (σ : F →+* AddMonoid.End (Additive ↥P)) (c : F) (p : ↥P) : G :=
  ((Additive.toMul (σ c (Additive.ofMul p)) : ↥P) : G)

@[expose] def FStructPreserved {F : Type} [Field F] {P : Subgroup G} [IsMulCommutative ↥P]
    (σ : F →+* AddMonoid.End (Additive ↥P)) (Y : Subgroup G) : Prop :=
  ∀ y ∈ Y, ∀ (c : F) (p p' : ↥P), (p' : G) = y * (p : G) * y⁻¹ →
    fsmul σ c p' = y * fsmul σ c p * y⁻¹

@[expose] def FStructStable {F : Type} [Field F] {P : Subgroup G} [IsMulCommutative ↥P]
    (σ : F →+* AddMonoid.End (Additive ↥P)) (W : Subgroup G) : Prop :=
  ∀ (c : F) (w : ↥P), (w : G) ∈ W → fsmul σ c w ∈ W

abbrev bOf (T I H : Subgroup G) : Subgroup G :=
  fsuV T I ⊓ Subgroup.centralizer (VZ T H : Set G)

abbrev pOf (T I H : Subgroup G) (h : G) : Subgroup G :=
  bOf T I H ⊔ conjSubgroup (bOf T I H) h

abbrev yOf (T L I V₂ : Subgroup G) (h : G) : Subgroup G :=
  LOf L V₂ ⊔ (fsuV T I ⊔ conjSubgroup (fsuV T I) h)

end Defs

@[expose] def Stmt11_3_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₂ H : Subgroup G)
    (g h : G), Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsVi T L I n 2 V₂ →
    Hyp11_3_1 T L I n V₁ H → ¬ Concl11_3_2 T L I n V₁ H → conjSubgroup (fsuV T I) g ≤ T →
    ¬ conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (VZ T H : Set G) → h ∈ H →
    h ∉ Subgroup.normalizer (L : Set G) →
      pOf T I H h ⊓ fsuV T I = V₂ ∧
      yOf T L I V₂ h ≤ Subgroup.normalizer (pOf T I H h : Set G) ∧
      ∃ (_ : IsMulCommutative ↥(pOf T I H h)) (_ : IsMulCommutative ↥(fsuV T I))
        (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        ∃ (σP : F →+* AddMonoid.End (Additive ↥(pOf T I H h)))
          (σV : F →+* AddMonoid.End (Additive ↥(fsuV T I))),
          FStructPreserved σP (yOf T L I V₂ h) ∧ FStructPreserved σV L ∧
          ∀ (c : F) (x : ↥(pOf T I H h)) (x' : ↥(fsuV T I)), (x : G) = (x' : G) →
            fsmul σP c x = fsmul σV c x'

@[expose] def Stmt11_3_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₂ H X W₁ W₂ : Subgroup G)
    (g h : G), Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsVi T L I n 2 V₂ →
    Hyp11_3_1 T L I n V₁ H → ¬ Concl11_3_2 T L I n V₁ H → conjSubgroup (fsuV T I) g ≤ T →
    ¬ conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (VZ T H : Set G) → h ∈ H →
    h ∉ Subgroup.normalizer (L : Set G) → IsCartanX T L X →
    W₁ ≤ fsuV T I → X ≤ Subgroup.normalizer (W₁ : Set G) →
    W₁ ⊓ (fsuV T I ⊓ pOf T I H h) = ⊥ → W₁ ⊔ (fsuV T I ⊓ pOf T I H h) = fsuV T I →
    W₂ ≤ pOf T I H h → X ≤ Subgroup.normalizer (W₂ : Set G) →
    W₂ ⊓ (pOf T I H h ⊓ ROf T L V₁) = ⊥ → W₂ ⊔ (pOf T I H h ⊓ ROf T L V₁) = pOf T I H h →
      (∀ x ∈ X, ∀ w ∈ W₁, ∀ w' ∈ W₂, (x * w * x⁻¹) * (x * w' * x⁻¹) * (x * w * x⁻¹)⁻¹ *
        (x * w' * x⁻¹)⁻¹ = x * (w * w' * w⁻¹ * w'⁻¹) * x⁻¹) ∧
      ∃ (_ : IsMulCommutative ↥(pOf T I H h)) (_ : IsMulCommutative ↥(fsuV T I))
        (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        ∃ (σP : F →+* AddMonoid.End (Additive ↥(pOf T I H h)))
          (σV : F →+* AddMonoid.End (Additive ↥(fsuV T I))),
          FStructPreserved σP (yOf T L I V₂ h) ∧ FStructPreserved σV L ∧
          (∀ (c : F) (x : ↥(pOf T I H h)) (x' : ↥(fsuV T I)), (x : G) = (x' : G) →
            fsmul σP c x = fsmul σV c x') ∧
          FStructStable σV W₁ ∧ FStructStable σP W₂ ∧
          (∀ w₁ ∈ W₁, ∀ w₂ ∈ W₁, ∀ w' ∈ W₂, (w₁ * w₂) * w' * (w₁ * w₂)⁻¹ * w'⁻¹ =
            (w₁ * w' * w₁⁻¹ * w'⁻¹) * (w₂ * w' * w₂⁻¹ * w'⁻¹)) ∧
          (∀ w ∈ W₁, ∀ w₁' ∈ W₂, ∀ w₂' ∈ W₂, w * (w₁' * w₂') * w⁻¹ * (w₁' * w₂')⁻¹ =
            (w * w₁' * w⁻¹ * w₁'⁻¹) * (w * w₂' * w⁻¹ * w₂'⁻¹)) ∧
          ∀ (c : F) (w : ↥(fsuV T I)) (w' z : ↥(pOf T I H h)), (w : G) ∈ W₁ → (w' : G) ∈ W₂ →
            (z : G) = (w : G) * w' * (w : G)⁻¹ * (w' : G)⁻¹ →
              fsmul σV c w * w' * (fsmul σV c w)⁻¹ * (w' : G)⁻¹ = fsmul σP c z ∧
              (w : G) * fsmul σP c w' * (w : G)⁻¹ * (fsmul σP c w')⁻¹ = fsmul σP c z

end CFSG.Quasithin.Vol2.Ch11
