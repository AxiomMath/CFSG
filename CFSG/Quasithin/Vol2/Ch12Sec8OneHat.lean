module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneStatements
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.Quasithin.Background.G2SL3Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

structure HatModelU (U : Subgroup G) where
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module (ZMod 2) V]
  [finite : Finite V]
  π : G → V
  B : LinearMap.BilinForm (ZMod 2) V
  ρ : ↥(Subgroup.normalizer (U : Set G)) →* (V ≃ₗ[ZMod 2] V)
  π_mul : ∀ a ∈ U, ∀ b ∈ U, π (a * b) = π a + π b
  π_surj : ∀ v : V, ∃ u ∈ U, π u = v
  π_eq_iff : ∀ a ∈ U, ∀ b ∈ U, π a = π b ↔ a⁻¹ * b ∈ centerOf U
  B_spec : ∀ a ∈ U, ∀ b ∈ U, B (π a) (π b) = 0 ↔ a * b * a⁻¹ * b⁻¹ = 1
  ρ_π : ∀ (x : ↥(Subgroup.normalizer (U : Set G))), ∀ u ∈ U,
    ρ x (π u) = π ((x : G) * u * (x : G)⁻¹)

attribute [instance] HatModelU.addCommGroup HatModelU.module HatModelU.finite

namespace HatModelU

variable {U : Subgroup G} (D : HatModelU U)

@[expose] noncomputable def img (K : Subgroup G) : Subgroup (D.V ≃ₗ[ZMod 2] D.V) :=
  (K.subgroupOf (Subgroup.normalizer (U : Set G))).map D.ρ

@[expose] def hat (A : Subgroup G) : Submodule (ZMod 2) D.V :=
  Submodule.span (ZMod 2) (D.π '' ((A ⊓ U : Subgroup G) : Set G))

end HatModelU

@[expose] def Lemma12_8_8_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ D : HatModelU (u128 V V₁),
      (∀ v, D.B v v = 0) ∧ (∀ v, (∀ w, D.B v w = 0) → v = 0) ∧
      (∀ γ ∈ D.img (Subgroup.normalizer (V₁ : Set G)), ∀ v w, D.B (γ v) (γ w) = D.B v w) ∧
      (frattiniOf (zU128 V V₁) = ⊥ → ∃ q : D.V → ZMod 2,
        (∀ u ∈ u128 V V₁, q (D.π u) = 0 ↔ u ^ 2 = 1) ∧
        (∀ v w, q (v + w) = q v + q w + D.B v w) ∧
        ∀ γ ∈ D.img (Subgroup.normalizer (V₁ : Set G)), ∀ v, q (γ v) = q v)

@[expose] def Lemma12_8_8_four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → n ≤ 3 →
      L ≤ conjClosure (u128 V V₁) L ∧
        AlmostSpecialL3Hyp 1 V V₁ L T (Subgroup.normalizer (V₁ : Set G))

@[expose] def Lemma12_8_11_hat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
    ∀ a ∈ V₂, a ∉ V₁ → ∀ D : HatModelU (u128 V V₁),
      ((∀ x ∈ D.img (CFSG.conjugate (w128 V V₁ V₂) g), ∃ f : D.V →ₗ[ZMod 2] ZMod 2,
          f (D.π a) = 0 ∧
          ∀ w ∈ D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g), x w = w + f w • D.π a) ∧
        ∀ f : D.V →ₗ[ZMod 2] ZMod 2, f (D.π a) = 0 →
          ∃ x ∈ D.img (CFSG.conjugate (w128 V V₁ V₂) g),
            ∀ w ∈ D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g),
              x w = w + f w • D.π a) ∧
      Module.finrank (ZMod 2) ↥(D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g)) +
          Nat.log 2 ((D.img (CFSG.conjugate (zU128 V V₁) g)).relIndex
            (D.img (CFSG.conjugate (w128 V V₁ V₂) g))) =
        Module.finrank (ZMod 2) D.V - 1 ∧
      ((∃ v : D.V, (∀ x ∈ D.img (CFSG.conjugate (w128 V V₁ V₂) g), x v = v) ∧ v ≠ 0 ∧
          v ≠ D.π a) →
        ∃ x ∈ D.img (CFSG.conjugate (w128 V V₁ V₂) g), x ≠ 1 ∧
          Module.finrank (ZMod 2) ↥(LinearMap.range (x.toLinearMap - LinearMap.id)) ≤ 2 ∧
          D.π a ∈ LinearMap.range (x.toLinearMap - LinearMap.id))

@[expose] def Lemma12_8_12_hat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
    ∀ a ∈ V₂, a ∉ V₁ → ∀ D : HatModelU (u128 V V₁),
      G101Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
          (D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g))
          (D.img (CFSG.conjugate (w128 V V₁ V₂) g)) (D.img (CFSG.conjugate (zU128 V V₁) g)) ∧
      G111Hyp D.B (D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)
          (D.hat (w128 V V₁ V₂ ⊓ CFSG.conjugate (w128 V V₁ V₂) g))
          (D.img (CFSG.conjugate (w128 V V₁ V₂) g)) (D.img (CFSG.conjugate (zU128 V V₁) g)) ∧
      G11.G112ConclusionFix D.B (D.img (Subgroup.normalizer (V₁ : Set G)))
        (D.img (CFSG.conjugate (w128 V V₁ V₂) g))

@[expose] def Lemma12_8_13_hat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Setting1282One G T L V n V₁ V₂ → ∀ g ∈ p128 T L V, g ∉ Subgroup.normalizer (V₁ : Set G) →
    ∀ D : HatModelU (u128 V V₁),
      (G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))) →
        ∃ K : Subgroup G,
          K = Subgroup.closure {x | x ∈ Subgroup.normalizer (V₁ : Set G) ∧
            ∃ k : ℕ, orderOf x = 3 ^ k} ∧
          quasithinIsCComponent K (Subgroup.normalizer (V₁ : Set G)) ∧
          quasithinO2QuotientIso K (alternatingGroup (Fin 8)) ∧
          quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁) ≠ ⊥ ∧
          conjClosure (quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁)) K ≤
            zU128 V V₁ ∧
          IsTwoReducedIn (K ⊔ T)
            (conjClosure (quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁)) K) ∧
          ⁅quasithinOmegaOneCenter T ⊓ centerOf (i128 T L V V₁), K⁆ ≠ ⊥ ∧
          K = ⁅K, CFSG.conjugate (zU128 V V₁) g⁆ ∧
          quasithinIsFaithfulLocal T K) ∧
      ¬ G112Concl4 (D.img (Subgroup.normalizer (V₁ : Set G))) ∧
      ¬ G112Concl12 (D.img (Subgroup.normalizer (V₁ : Set G)))
        (D.img (CFSG.conjugate (w128 V V₁ V₂) g))

end CFSG.Quasithin.H13
