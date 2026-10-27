module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.AlgebraicGroups.ToralRootCover

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.Open (StatedLieTag IsElemAbelian)

@[expose] noncomputable def rckTorusCoord {τ : Tag} {L : Type} [Field L] (y : ModGL τ L) :
    Fin τ.rank → Lˣ :=
  Function.invFun (rootDiagUnitHom τ L) y

@[expose] noncomputable def rckFamChar {τ : Tag} {L : Type} [Field L] {ι : Type} (g : ModGL τ L)
    (x : ι → ModGL τ L) : Multiplicative (Fin τ.rank → ℤ) →* (ι → Lˣ) :=
  MonoidHom.pi fun i => rootCharHom (rckTorusCoord (g⁻¹ * x i * g))

@[expose] def RCKExcShape {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (Ψ : Set (Fin τ.rank → ℤ)) : Prop :=
  (compRank Ψ = 4 ∧ Ψ.ncard = 48) ∨ (compRank Ψ = 6 ∧ Ψ.ncard = 72) ∨
    (compRank Ψ = 7 ∧ Ψ.ncard = 126) ∨ (compRank Ψ = 8 ∧ Ψ.ncard = 240) ∨
    (compRank Ψ = 4 ∧ Ψ.ncard = 24 ∧
      ¬ twistInner Ψ ((ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength ρ Ψ]))

@[expose] def RCKExcRelOneAt
    (P : StatedLieTag → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), P t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J →
    ∀ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL)),
      RCKBridgeFrame t f p G₀ A θ A' → ExcFramesHalf.IsToralSubgroup (langTag t) GGL A' →
      ∀ (Dl : LangDatum (langTag t) GGL) (ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)),
        Dl.Φ = ggPhi t f → FrobRootMap Dl ρ → (∀ x ∈ A', Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus) →
        ∀ (S₁ S₂ : Subgroup (ModGL (langTag t) GGL)), S₂ ≤ S₁ → S₁ ≤ A' →
          Nat.card S₁ = p ^ 2 → Nat.card S₂ = p →
          ∀ (iJ : KernelComponent (rckFamChar Dl.g0 (fun x : S₁ => (x : ModGL (langTag t) GGL))))
            (iK : KernelComponent (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag t) GGL)))),
            componentRoots (rckFamChar Dl.g0 (fun x : S₁ => (x : ModGL (langTag t) GGL))) iJ ⊆
              componentRoots (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag t) GGL))) iK →
            RCKExcShape ρ
              (componentRoots (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag t) GGL))) iK) →
            componentOrbitLength ρ
                (componentRoots (rckFamChar Dl.g0 (fun x : S₁ => (x : ModGL (langTag t) GGL))) iJ) =
              componentOrbitLength ρ
                (componentRoots (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag t) GGL))) iK)

@[expose] def rckChebC (d : ℕ) : ℤ := if d = 3 then -1 else if d = 4 then 0 else 1

@[expose] def RCKExcClassShape (τ : Tag) (d : ℕ) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) : Prop :=
  (d = 1 → ∀ γ, IsRoot τ γ → ρ γ = γ) ∧
  (d = 2 → (∀ γ, IsRoot τ γ → ρ γ = -γ) ∨
    ∃ β, IsRoot τ β ∧ ∀ γ, IsRoot τ γ → ρ γ = -(rootReflection β • γ)) ∧
  ((τ = .E8 ∧ (d = 3 ∨ d = 4 ∨ d = 6)) →
    ∀ γ, IsRoot τ γ → ρ (ρ γ) + γ = rckChebC d • ρ γ) ∧
  (d ≠ 1 → d ≠ 2 → τ = .E8 ∧ (d = 3 ∨ d = 4 ∨ d = 6))

@[expose] def RCKExcClassAt
    (P : StatedLieTag → Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), P t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J →
    ∀ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL)),
      RCKBridgeFrame t f p G₀ A θ A' → ExcFramesHalf.IsToralSubgroup (langTag t) GGL A' →
      ∀ (Dl : LangDatum (langTag t) GGL) (ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)),
        Dl.Φ = ggPhi t f → FrobRootMap Dl ρ → (∀ x ∈ A', Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus) →
        RCKExcClassShape (langTag t) (orderOf ((2 ^ f : ℕ) : ZMod p)) ρ

@[expose] def RCKExcOrbitAt
    (P : StatedLieTag → Prop) : Prop :=
  ∀ (t : StatedLieTag), P t → ∀ (f p : ℕ), 1 ≤ f → p.Prime → p ≠ 2 →
    ∀ (Dl : LangDatum (langTag t) GGL) (ρ : Equiv.Perm (Fin (langTag t).rank → ℤ)),
      Dl.Φ = ggPhi t f → FrobRootMap Dl ρ →
      RCKExcClassShape (langTag t) (orderOf ((2 ^ f : ℕ) : ZMod p)) ρ →
      ∀ (S₁ S₂ : Subgroup (ModGL (langTag t) GGL)), S₂ ≤ S₁ → IsElemAbelian p S₁ →
        (∀ x ∈ S₁, Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus) → Nat.card S₁ = p ^ 2 → Nat.card S₂ = p →
        ∀ (iJ : KernelComponent (rckFamChar Dl.g0 (fun x : S₁ => (x : ModGL (langTag t) GGL))))
          (iK : KernelComponent (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag t) GGL)))),
          componentRoots (rckFamChar Dl.g0 (fun x : S₁ => (x : ModGL (langTag t) GGL))) iJ ⊆
            componentRoots (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag t) GGL))) iK →
          RCKExcShape ρ
            (componentRoots (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag t) GGL))) iK) →
          componentOrbitLength ρ
              (componentRoots (rckFamChar Dl.g0 (fun x : S₁ => (x : ModGL (langTag t) GGL))) iJ) =
            componentOrbitLength ρ
              (componentRoots (rckFamChar Dl.g0 (fun x : S₂ => (x : ModGL (langTag t) GGL))) iK)

theorem rckExcRelOneAt_of_class_orbit
    {P : StatedLieTag → Prop} (hC : RCKExcClassAt P) (hO : RCKExcOrbitAt P) :
    RCKExcRelOneAt P := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht h hKJ θ A' hframe htoral Dl ρ hΦ hρ hA'
    S₁ S₂ hS hS₁A hc₁ hc₂ iJ iK hsub hshape
  have hcfg := h
  unfold RCKRPConfig at hcfg
  obtain ⟨hGG, -, hp, hp2, -⟩ := hcfg
  have hf : 1 ≤ f := hGG.1.1.2.1
  have hcl := hC X t n f ψ p G₀ A B₁ D J L R Rm K e ht h hKJ θ A' hframe htoral Dl ρ hΦ hρ hA'
  have hel : IsElemAbelian p S₁ := by
    obtain ⟨hA'c, hA'p⟩ := hframe.2.2.2.1
    refine ⟨(isMulCommutative_iff).2 ?_, fun x hx => hA'p x (hS₁A hx)⟩
    intro x y
    have h : (x : ModGL (langTag t) GGL) * (y : ModGL (langTag t) GGL) =
        (y : ModGL (langTag t) GGL) * (x : ModGL (langTag t) GGL) :=
      congrArg Subtype.val ((isMulCommutative_iff.mp hA'c) ⟨x, hS₁A x.2⟩ ⟨y, hS₁A y.2⟩)
    exact Subtype.ext h
  exact hO t ht f p hf hp hp2 Dl ρ hΦ hρ hcl S₁ S₂ hS hel
    (fun x hx => hA' x (hS₁A hx)) hc₁ hc₂ iJ iK hsub hshape

theorem rckExcRelOne_of_split
    {P Q : StatedLieTag → Prop} (hP : RCKExcRelOneAt P) (hQ : RCKExcRelOneAt Q) :
    RCKExcRelOneAt (fun t => P t ∨ Q t) := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht
  rcases ht with ht | ht
  · exact hP X t n f ψ p G₀ A B₁ D J L R Rm K e ht
  · exact hQ X t n f ψ p G₀ A B₁ D J L R Rm K e ht

end CFSG.StandardType.RCKRP
