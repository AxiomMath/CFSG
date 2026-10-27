module

public import CFSG.Quasithin.H13.J4TypeDefs
public import CFSG.Quasithin.Background.SmithB45M22HatModel
public import CFSG.GF2Type.Smith1979.IdxFourHBasic
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin.HatM22
open CFSG.CharacterTheory.SteinbergBY (FieldFour)

abbrev H {G : Type} [Group G] (z : G) : Subgroup G := centralizer ({z} : Set G)

abbrev Q {G : Type} [Group G] (z : G) : Subgroup G := pCoreOf 2 (H z)

structure HypJ4 (G : Type) [Group G] [Finite G] (z : G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  orderOf_z : orderOf z = 2
  core : J4.IsTypeJ4Core (Subgroup.centralizer ({z} : Set G)) (J4.selfC z)
  autTriple : J4.IsAutTripleM22 (Subgroup.centralizer ({z} : Set G) ⧸
    CFSG.pCore 2 (Subgroup.centralizer ({z} : Set G)))
  not_weaklyClosed : ∃ g : G, g⁻¹ * z * g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
    g⁻¹ * z * g ≠ z

structure Loc41 (G : Type) [Group G] [Finite G] (z : G) where
  S : Setting G
  S_z : S.z = z
  S_QG : S.QG = Q z
  X : Subgroup G
  X_le : X ≤ H z
  card_X : Nat.card X = 3
  QX_normal : ∀ h ∈ H z, ∀ y ∈ Q z ⊔ X, h * y * h⁻¹ ∈ Q z ⊔ X
  eq_sup_normalizer : H z = Q z ⊔ (H z ⊓ normalizer (X : Set G))
  inf_centralizer : Q z ⊓ centralizer (X : Set G) = zpowers z
  ψ : S.Qt ≃+ (Fin 6 → FieldFour)
  acts : ∀ h : S.M, (h : G) ∈ centralizer (X : Set G) → ∃ γ ∈ hatM22Γ₀, ∀ v : S.Qt,
    ψ ((S.ρ h : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour).mulVec
        (ψ v)
  onto : ∀ γ ∈ hatM22Γ₀, ∃ h : S.M, (h : G) ∈ centralizer (X : Set G) ∧ ∀ v : S.Qt,
    ψ ((S.ρ h : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour).mulVec
        (ψ v)

structure Loc42 (G : Type) [Group G] [Finite G] (z : G) extends Loc41 G z where
  card_Mbar : Nat.card S.Mbar = 2661120
  linear_or_semilinear : ∀ h : S.M,
    (∃ γ ∈ hatM22Γ₀, ∀ v : S.Qt, ψ ((S.ρ h : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      ((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) : Matrix (Fin 6) (Fin 6) FieldFour).mulVec
        (ψ v)) ∨
    ∀ (c : FieldFour) (v : S.Qt), ψ ((S.ρ h : S.Qt ≃ₗ[ZMod 2] S.Qt) (ψ.symm (c • ψ v))) =
      (c * c) • ψ ((S.ρ h : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
  r₁ : G
  r₂ : G
  r₁_mem : r₁ ∈ Q z
  r₂_mem : r₂ ∈ Q z
  r₁_sq : r₁ * r₁ = 1
  r₂_sq : r₂ * r₂ = 1
  r₁_ne_one : r₁ ≠ 1
  r₂_ne_one : r₂ ≠ 1
  r₁_ne_z : r₁ ≠ z
  r₂_ne_z : r₂ ≠ z
  conj_or : ∀ r ∈ Q z, r * r = 1 → r ≠ 1 → r ≠ z →
    (∃ h ∈ H z, h * r * h⁻¹ = r₁) ∨ ∃ h ∈ H z, h * r * h⁻¹ = r₂
  not_conj : ∀ h ∈ H z, h * r₁ * h⁻¹ ≠ r₂
  card_stab₁ : Nat.card (GF2Type.Smith1979.IdxFour.stab S (S.cl r₁)) = 3840
  card_stab₂ : Nat.card (GF2Type.Smith1979.IdxFour.stab S (S.cl r₂)) = 1920
  core₁ : ∃ P : Subgroup S.O, P ≤ GF2Type.Smith1979.IdxFour.stab S (S.cl r₁) ∧
    (∀ s ∈ GF2Type.Smith1979.IdxFour.stab S (S.cl r₁), ∀ p ∈ P, s * p * s⁻¹ ∈ P) ∧
    IsPGroup 2 P ∧ Nat.card P = 2 ^ 5
  core₁_le : ∀ P : Subgroup S.O, P ≤ GF2Type.Smith1979.IdxFour.stab S (S.cl r₁) →
    (∀ s ∈ GF2Type.Smith1979.IdxFour.stab S (S.cl r₁), ∀ p ∈ P, s * p * s⁻¹ ∈ P) →
    IsPGroup 2 P → Nat.card P ≤ 2 ^ 5
  core₂ : ∃ P : Subgroup S.O, P ≤ GF2Type.Smith1979.IdxFour.stab S (S.cl r₂) ∧
    (∀ s ∈ GF2Type.Smith1979.IdxFour.stab S (S.cl r₂), ∀ p ∈ P, s * p * s⁻¹ ∈ P) ∧
    IsPGroup 2 P ∧ Nat.card P = 2 ^ 4
  core₂_le : ∀ P : Subgroup S.O, P ≤ GF2Type.Smith1979.IdxFour.stab S (S.cl r₂) →
    (∀ s ∈ GF2Type.Smith1979.IdxFour.stab S (S.cl r₂), ∀ p ∈ P, s * p * s⁻¹ ∈ P) →
    IsPGroup 2 P → Nat.card P ≤ 2 ^ 4

structure Loc43 (G : Type) [Group G] [Finite G] (z : G) extends Loc42 G z where
  g₁ : G
  r₁_eq : g₁ * z * g₁⁻¹ = r₁
  conj_z : ∀ g : G, g * z * g⁻¹ ∈ Q z →
    g * z * g⁻¹ = z ∨ ∃ h ∈ H z, h * r₁ * h⁻¹ = g * z * g⁻¹
  card_inf : Nat.card (Q z ⊓ (Q z).map (MulAut.conj g₁).toMonoidHom : Subgroup G) = 2 ^ 7
  k₁ : G
  Z : Subgroup G
  Z_eq_inf : Z = Q z ⊓ (Q z).map (MulAut.conj g₁).toMonoidHom ⊓
    (Q z).map (MulAut.conj k₁).toMonoidHom
  Z_eq_closure : Z = closure {z, g₁ * z * g₁⁻¹, k₁ * z * k₁⁻¹}
  Z_eq_sup : Z = zpowers z ⊔ ⁅zpowers r₁, X⁆
  card_Z : Nat.card Z = 8
  Z_sq : ∀ x ∈ Z, x * x = 1

structure Loc45 (G : Type) [Group G] [Finite G] (z : G) extends Loc43 G z where
  G13 : Subgroup G
  G13_le : G13 ≤ H z
  QX_le : Q z ⊔ X ≤ G13
  card_G13 : Nat.card G13 = 2 ^ 13 * 3 * (2 ^ 4 * 720)
  T : Sylow 2 G
  T_le : (T : Subgroup G) ≤ G13
  center_T : (center (T : Subgroup G)).map (T : Subgroup G).subtype = zpowers z
  fix_T : ∀ v : S.Qt, (∀ t : S.M, (t : G) ∈ (T : Subgroup G) →
    (S.ρ t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) ↔ v = 0 ∨ v = S.cl r₁
  T_le_normalizer : (T : Subgroup G) ≤ normalizer (Z : Set G)

end CFSG.Quasithin.H13.AS91
