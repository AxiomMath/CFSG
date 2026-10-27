module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Subgroup

@[expose] def OneOrTwoLayerAlternatives {H : Type*} [Group H] (J D : Subgroup H) (a : H) :
    Prop :=
  Xor
    (IsSimpleGroup D ∧ (∃ x y : D, x * y ≠ y * x) ∧ J < D ∧ ∃ d ∈ D, a⁻¹ * d * a ≠ d)
    (∃ D₁ D₂ : Subgroup H, CFSG.IsComponent D₁ ∧ CFSG.IsComponent D₂ ∧ D₁ ≠ D₂ ∧
      IsSimpleGroup D₁ ∧ (∃ x y : D₁, x * y ≠ y * x) ∧
      IsSimpleGroup D₂ ∧ (∃ x y : D₂, x * y ≠ y * x) ∧
      D₁ ⊔ D₂ = D ∧ D₁ ⊓ D₂ = ⊥ ∧ ⁅D₁, D₂⁆ = ⊥ ∧
      D₁.map (MulAut.conj a⁻¹).toMonoidHom = D₂ ∧ J = D ⊓ centralizer ({a} : Set H) ∧
      ∃ ψ : D ≃* J × J,
        (∀ (j : H) (hjJ : j ∈ J) (hjD : j ∈ D), ψ ⟨j, hjD⟩ = (⟨j, hjJ⟩, ⟨j, hjJ⟩)) ∧
        ∀ (d : H) (hd : d ∈ D) (hda : a⁻¹ * d * a ∈ D),
          ψ ⟨a⁻¹ * d * a, hda⟩ = (ψ ⟨d, hd⟩).swap)

@[expose] def OneOrTwoLayerConclusion {H : Type*} [Group H] (J : Subgroup H) (a : H) : Prop :=
  CFSG.pCore 2 H = ⊥ ∧ CFSG.fittingSubgroup H = ⊥ ∧ J ≤ CFSG.layer H ∧
    normalClosure (J : Set H) = CFSG.layer H ∧
    centralizer (normalClosure (J : Set H) : Set H) = ⊥ ∧
    OneOrTwoLayerAlternatives J (normalClosure (J : Set H)) a ∧
    ∀ h : H, (∀ d ∈ normalClosure (J : Set H), h⁻¹ * d * h = d) → h = 1

@[expose] def NonnormalInvolutionComponentLayerStmt : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Assembly.KProper CFSG.Blueprint.Catalog H →
    CFSG.pPrimeCore 2 H = ⊥ →
    ∀ J : Subgroup H, IsSimpleGroup J → (∃ x y : J, x * y ≠ y * x) →
    (∃ E : Subgroup H, E ≤ J ∧ CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4) →
    ∀ a : H, orderOf a = 2 → J ≤ centralizer ({a} : Set H) →
    centralizer ({a} : Set H) ≤ normalizer (J : Set H) →
    ¬ 2 ∣ (zpowers a).relIndex (centralizer (J : Set H)) → ¬ J.Normal →
    OneOrTwoLayerConclusion J a

@[expose] def DirectSimpleInvolutionCentralizerLayerStmt : Prop :=
  ∀ (F : Type) [Group F] [Finite F], CFSG.SectionRank.IsKGroupCat F →
    ∀ J : Subgroup F, IsSimpleGroup J → (∃ x y : J, x * y ≠ y * x) →
    (∃ E : Subgroup F, E ≤ J ∧ CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4) →
    ∀ a : F, orderOf a = 2 → J ≤ centralizer ({a} : Set F) → zpowers a ⊓ J = ⊥ →
    zpowers a ⊔ J = centralizer ({a} : Set F) →
    (∀ S : Sylow 2 F, a ∈ S → ∃ s ∈ S, s * a ≠ a * s) →
    let θ : F →* F ⧸ CFSG.pPrimeCore 2 F := QuotientGroup.mk' (CFSG.pPrimeCore 2 F)
    (IsMulCommutative (CFSG.pPrimeCore 2 F) ∧
      (∀ r ∈ CFSG.pPrimeCore 2 F, a⁻¹ * r * a = r⁻¹) ∧
      CFSG.pPrimeCore 2 F ⊓ centralizer ({a} : Set F) = ⊥) ∧
    (Set.InjOn θ J ∧ Set.InjOn θ (centralizer ({a} : Set F)) ∧
      ∀ P : Subgroup F, IsPGroup 2 P → Set.InjOn θ P) ∧
    (CFSG.SectionRank.IsKGroupCat (F ⧸ CFSG.pPrimeCore 2 F) ∧
      CFSG.Assembly.KProper CFSG.Blueprint.Catalog (F ⧸ CFSG.pPrimeCore 2 F) ∧
      CFSG.pPrimeCore 2 (F ⧸ CFSG.pPrimeCore 2 F) = ⊥) ∧
    (J.map θ ≤ centralizer ({θ a} : Set (F ⧸ CFSG.pPrimeCore 2 F)) ∧
      zpowers (θ a) ⊓ J.map θ = ⊥ ∧
      zpowers (θ a) ⊔ J.map θ = centralizer ({θ a} : Set (F ⧸ CFSG.pPrimeCore 2 F))) ∧
    (∀ S : Sylow 2 (F ⧸ CFSG.pPrimeCore 2 F), θ a ∈ S → ∃ s ∈ S, s * θ a ≠ θ a * s) ∧
    (CFSG.IsStandardSubgroup (J.map θ) ∧
      ¬ 2 ∣ (zpowers (θ a)).relIndex (centralizer (J.map θ : Set (F ⧸ CFSG.pPrimeCore 2 F))) ∧
      (∀ t ∈ centralizer (J.map θ : Set (F ⧸ CFSG.pPrimeCore 2 F)), orderOf t = 2 →
        ∃ c ∈ centralizer (J.map θ : Set (F ⧸ CFSG.pPrimeCore 2 F)), c⁻¹ * t * c = θ a) ∧
      ¬ (J.map θ).Normal) ∧
    OneOrTwoLayerConclusion (J.map θ) (θ a) ∧
    ((∀ x ∈ (normalClosure (J.map θ : Set (F ⧸ CFSG.pPrimeCore 2 F))).comap θ,
        ∀ r ∈ CFSG.pPrimeCore 2 F, x * r = r * x) ∧
      ⁅J, CFSG.pPrimeCore 2 F⁆ = ⊥) ∧
    ((normalClosure (J : Set F)).Normal ∧
      ⁅normalClosure (J : Set F), normalClosure (J : Set F)⁆ = normalClosure (J : Set F) ∧
      (normalClosure (J : Set F)).map θ =
        normalClosure (J.map θ : Set (F ⧸ CFSG.pPrimeCore 2 F)) ∧
      (normalClosure (J.map θ : Set (F ⧸ CFSG.pPrimeCore 2 F))).comap θ =
        CFSG.pPrimeCore 2 F ⊔ normalClosure (J : Set F) ∧
      (center (normalClosure (J : Set F))).map (normalClosure (J : Set F)).subtype =
        normalClosure (J : Set F) ⊓ CFSG.pPrimeCore 2 F ∧
      centralizer (normalClosure (J : Set F) : Set F) = CFSG.pPrimeCore 2 F ∧
      ∃ e : normalClosure (J : Set F) ⧸ (CFSG.pPrimeCore 2 F).subgroupOf (normalClosure (J : Set F))
          ≃* normalClosure (J.map θ : Set (F ⧸ CFSG.pPrimeCore 2 F)),
        ∀ q : normalClosure (J : Set F),
          (e (QuotientGroup.mk q) : F ⧸ CFSG.pPrimeCore 2 F) = θ q) ∧
    (Odd (Nat.card (normalClosure (J : Set F) ⊓ CFSG.pPrimeCore 2 F : Subgroup F)) ∧
      ∀ r ∈ normalClosure (J : Set F) ⊓ CFSG.pPrimeCore 2 F, a⁻¹ * r * a = r⁻¹) ∧
    CFSG.pCore 2 F = ⊥ ∧ CFSG.fittingSubgroup F = CFSG.pPrimeCore 2 F

end CFSG.LocalAnalysis.SteinbergBV
