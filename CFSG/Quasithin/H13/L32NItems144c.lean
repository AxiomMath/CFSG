module

public import CFSG.Quasithin.H13.L32NItems143b
public import CFSG.Quasithin.H13.L32NItems1442Models
public import CFSG.Quasithin.Background.A4Four

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

structure IsModelIso {U : Subgroup G} (D : HatModelU U) (X : Subgroup G) {n : ℕ}
    (e : D.V ≃ₗ[ZMod 2] (Fin n → ZMod 2)) (Q : Matrix (Fin n) (Fin n) (ZMod 2))
    (Γ : Subgroup (GL (Fin n) (ZMod 2))) : Prop where
  quad : ∀ u ∈ U, L1442M.quadOf Q (e (D.π u)) = 0 ↔ u * u = 1
  img : ∀ φ : D.V ≃ₗ[ZMod 2] D.V, φ ∈ D.img X ↔
    ∃ γ ∈ Γ, ∀ v, e (φ v) = (γ : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec (e v)

@[expose] def Case1442Three (T V V₂ : Subgroup G) (g : G) (D : HatModelU (fsuU T V)) : Prop :=
  ∃ e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2),
    IsModelIso D (oTwoUpper (l32nH T V)) e L1442M.q3 L1442M.omega3 ∧
    (∀ φ ∈ D.img (l32nH T V), ∃ γ ∈ L1442M.omega3N,
      ∀ v, e (φ v) = (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e v)) ∧
    ∃ xs ∈ D.img (CFSG.conjugate (l32nW T V V₂) g),
      (∃ γ ∈ L1442M.omega3N, γ ∉ L1442M.omega3F ∧
        ∀ v, e (xs v) = (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e v)) ∧
      Module.finrank (ZMod 2) ↥(LinearMap.range (xs.toLinearMap - LinearMap.id)) = 4 ∧
      D.img (CFSG.conjugate (l32nW T V V₂) g) =
        (D.img T ⊓ D.img (oTwoUpper (l32nH T V)) ⊓ Subgroup.centralizer {xs}) ⊔
          Subgroup.zpowers xs

@[expose] def Case1442Four (T V V₂ : Subgroup G) (g : G) (D : HatModelU (fsuU T V)) : Prop :=
  ∃ e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2), IsModelIso D (l32nH T V) e L1442M.q4 L1442M.s7 ∧
    Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 3 ∧
    ∃ xs ∈ D.img (CFSG.conjugate (l32nW T V V₂) g), ∃ v,
      e v ∈ L1442M.subI ∧ e (xs v) ∉ L1442M.subI

@[expose] def Case1442EightPrime (T V V₂ : Subgroup G) (g : G) (D : HatModelU (fsuU T V)) :
    Prop :=
  ∃ e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2), IsModelIso D (l32nH T V) e L1442M.q4 L1442M.s8 ∧
    ∃ xs ∈ D.img (CFSG.conjugate (l32nW T V V₂) g), ∃ v,
      e v ∈ L1442M.subI ∧ e (xs v) ∉ L1442M.subI

@[expose] def Case1442Five (T V V₂ : Subgroup G) (g : G) (D : HatModelU (fsuU T V)) : Prop :=
  ∃ (b₁ b₂ : Bool) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)),
    IsModelIso D (l32nH T V) e (L1442M.q5 b₂) (L1442M.g5 b₁ b₂) ∧
    Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 3

@[expose] def Case1442Six (T V V₂ : Subgroup G) (g : G) (D : HatModelU (fsuU T V)) : Prop :=
  ∃ e : D.V ≃ₗ[ZMod 2] (Fin 12 → ZMod 2), IsModelIso D (l32nH T V) e L1442M.q12 L1442M.m22 ∧
    Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 5

@[expose] def Lemma1442Big : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) ≠ 2 ^ 5 →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V),
      Case1442Three T V V₂ g D ∨ Case1442Four T V V₂ g D ∨ Case1442EightPrime T V V₂ g D ∨
        Case1442Five T V V₂ g D ∨ Case1442Six T V V₂ g D

@[expose] def IsY1442 (T V V₂ : Subgroup G) (g : G) (X : Subgroup G) : Prop :=
  X ≤ l32nH T V ∧ T ≤ Subgroup.normalizer (X : Set G) ∧ oTwoUpper X = X ∧
    (pCoreOf 2 X).relIndex X = 3 ∧ Nat.card ↥⁅V₂, X⁆ = 8 ∧ ⁅V₂, X⁆ ≤ l32nE T V V₂ g

@[expose] def Y1444Claim (T L V V₂ : Subgroup G) (g : G) : Prop :=
  ∃ X : Subgroup G, IsY1442 T V V₂ g X ∧ X ≠ lOne L (fsuV1 T V) ∧
    Nonempty (OTwoQuot (lOne L (fsuV1 T V) ⊔ X ⊔ T) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))

@[expose] def Lemma14413BigM22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp14310One G T L V →
    CFSG.IsExtraspecialPGroup 2 ↥(fsuU T V) → Nat.card ↥(fsuU T V) ≠ 2 ^ 5 →
    ∀ (V₂ : Subgroup G) (g : G), IsL32NPlane T V V₂ → g ∈ p128 T L V → g ∉ l32nH T V →
    ∀ D : HatModelU (fsuU T V), Case1442Six T V V₂ g D → Y1444Claim T L V V₂ g

end CFSG.Quasithin.H13
