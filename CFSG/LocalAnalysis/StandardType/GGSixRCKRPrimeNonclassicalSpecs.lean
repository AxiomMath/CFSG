module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnAssembly

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)

@[expose] def RCKCompImage : Prop :=
  ∀ {X Y : Type} [Group X] [Group Y] (K J : Subgroup X) (d : X) (c : ↥K →* Y) (y : Y),
    c.ker ≤ Subgroup.center ↥K → d ∈ Subgroup.normalizer (K : Set X) →
    (∀ (x : ↥K) (hx : d * (x : X) * d⁻¹ ∈ K), c ⟨d * (x : X) * d⁻¹, hx⟩ = y * c x * y⁻¹) →
    IsComponentOf J (K ⊓ Subgroup.centralizer {d}) →
    IsComponentOf ((J.subgroupOf K).map c) (c.range ⊓ Subgroup.centralizer {y})

@[expose] def RCKRelOneUse
    : Prop :=
  RCKExcRelOneAt GGExcFive →
  ∀ (X : Type) [Group X] [Finite X] (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* X)
    (p : ℕ) (G₀ A B₁ D J L R Rm K : Subgroup X) (e : X), GGExcFive t →
    RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e → K ≠ J →
    ∀ (θ : ↥G₀ →* ModGL (langTag t) GGL) (A' : Subgroup (ModGL (langTag t) GGL))
      (η : ↥G₀ →* ModGL (langTag t) GGL) (E' : Subgroup (ModGL (langTag t) GGL))
      (S : LangSetup (langTag t) GGL 5) (a : Fin (langTag t).rank → GGLˣ)
      (i : KernelComponent (rootCharHom a)),
      RCKFirstPassAt t f p G₀ A B₁ D J K e θ A' η E' S a i →
      ∀ (b : Fin (langTag t).rank → GGLˣ), rootDiagUnit (langTag t) b ∈ E' →
        (∀ j, b j ^ p = 1) →
        ∀ iJ : KernelComponent ((rootCharHom a).prod (rootCharHom b)),
          componentRoots ((rootCharHom a).prod (rootCharHom b)) iJ ⊆
            componentRoots (rootCharHom a) i →
          RCKExcShape S.ρ (componentRoots (rootCharHom a) i) →
          componentOrbitLength S.ρ (componentRoots ((rootCharHom a).prod (rootCharHom b)) iJ) =
            componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)

@[expose] def RCKClassTransport : Prop :=
  ∀ {τ τK : Tag} (a b : Fin τ.rank → GGLˣ) (aK : Fin τK.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (ι : (Fin τ.rank → ℤ) → (Fin τK.rank → ℤ)),
    Set.BijOn ι (componentRoots (rootCharHom a) i) {γ' | IsRoot τK γ'} →
    (∀ γ ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
      CFSG.LieType.Steinberg.Adjoint.iform (ι γ) (ι δ) = CFSG.LieType.Steinberg.Adjoint.iform γ δ) →
    (∀ γ ∈ componentRoots (rootCharHom a) i,
      rootCharHom aK (Multiplicative.ofAdd (ι γ)) = rootCharHom b (Multiplicative.ofAdd γ)) →
    ∀ j : KernelComponent (rootCharHom aK),
      ∃ iJ : KernelComponent ((rootCharHom a).prod (rootCharHom b)),
        componentRoots ((rootCharHom a).prod (rootCharHom b)) iJ =
          {γ | γ ∈ componentRoots (rootCharHom a) i ∧ ι γ ∈ componentRoots (rootCharHom aK) j}

@[expose] def RCKRootGroupTwo
    : Prop :=
  ∀ (M : LieUniversal) (g : ℕ), StandardReturnAt M g →
    ∀ β ∈ M.D.roots, IsPGroup 2 (M.D.rootGroup β)

end CFSG.StandardType.RCKRP
