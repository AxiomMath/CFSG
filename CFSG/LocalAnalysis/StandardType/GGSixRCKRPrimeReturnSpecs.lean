module

public import CFSG.LocalAnalysis.StandardType.GGPinnedReturnDefs
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.LocalAnalysis.StandardType.GGFinModelRat
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapLiftBasic
public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.LieCore
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

@[expose] def RCKFrameCover
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (h : ℕ) (Mod : LieUniversal → ℕ → Prop) : Prop :=
  ∃ (M : LieUniversal) (φ : M.K →* ModGL τ GGL),
    Mod M (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ∧
    StandardReturnAt M (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ∧
    φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
    φ.ker ≤ Subgroup.center M.K ∧
    Finite M.K ∧ Group.IsPerfect M.K ∧ CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit M.K ∧
    (∃ β ∈ M.D.roots, GGLongRoot M.D β) ∧
    ∀ b ∈ S.D.torus, GGPsiInnerDiag M.D φ b

@[expose] def RCKCarrierSL
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ),
    S.D.q = 2 ^ h → twistKind S.ρ (rootCharHom a) i = .inner →
    2 ≤ compRank (componentRoots (rootCharHom a) i) →
    (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
      (compRank (componentRoots (rootCharHom a) i) + 1) →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCover S a i h
      (fun M g => M = ggU .PSL (compRank (componentRoots (rootCharHom a) i) + 1) g)

@[expose] def RCKCarrierA1
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ),
    S.D.q = 2 ^ h → compRank (componentRoots (rootCharHom a) i) = 1 →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCover S a i h (fun M g => M = ggU .PSL 2 g)

@[expose] def RCKCarrierSU
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ),
    S.D.q = 2 ^ h → twistKind S.ρ (rootCharHom a) i = .suN →
    3 ≤ compRank (componentRoots (rootCharHom a) i) →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCover S a i h
      (fun M g => M = ggU .PSU (compRank (componentRoots (rootCharHom a) i) + 1) g)

@[expose] def RCKCarrierSpF4
    : Prop :=
  ∀ (p₀ : ℕ) (S : LangSetup Tag.F4 GGL p₀) (a : Fin Tag.F4.rank → GGLˣ),
    rootDiagUnit Tag.F4 a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit Tag.F4 a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ),
    S.D.q = 2 ^ h → twistKind S.ρ (rootCharHom a) i = .inner →
    compRank (componentRoots (rootCharHom a) i) = 3 →
    (componentRoots (rootCharHom a) i).ncard = 18 →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCover S a i h (fun M g => M = ggU .PSp 3 g)

@[expose] def RCKCarrierSpB2
    : Prop :=
  ∀ (p₀ : ℕ) (S : LangSetup Tag.F4 GGL p₀) (a : Fin Tag.F4.rank → GGLˣ),
    rootDiagUnit Tag.F4 a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit Tag.F4 a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ),
    S.D.q = 2 ^ h → compRank (componentRoots (rootCharHom a) i) = 2 →
    (componentRoots (rootCharHom a) i).ncard = 8 →
    4 ≤ 2 ^ (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCover S a i h (fun M g => M = ggU .PSp 2 g)

@[expose] def RCKCarrierSpinPlus
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ),
    S.D.q = 2 ^ h → twistKind S.ρ (rootCharHom a) i = .inner →
    4 ≤ compRank (componentRoots (rootCharHom a) i) →
    (componentRoots (rootCharHom a) i).ncard = 2 * compRank (componentRoots (rootCharHom a) i) *
      (compRank (componentRoots (rootCharHom a) i) - 1) →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCover S a i h
      (fun M g => M = ggU .POmegaPlus (compRank (componentRoots (rootCharHom a) i)) g)

@[expose] def RCKCarrierTwoD
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ),
    S.D.q = 2 ^ h → twistKind S.ρ (rootCharHom a) i = .twoD →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCover S a i h
      (fun M g => M = ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) g)

@[expose] def RCKPinnedOfFrameCover
    : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (τ : Tag) (G₀ K B : Subgroup X) (hK : K ≤ G₀)
    (η : ↥G₀ →* ModGL τ GGL) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (h : ℕ) (Mod : LieUniversal → ℕ → Prop),
    η.ker ≤ Subgroup.center ↥G₀ →
    (K.subgroupOf G₀).map η = rationalComponent S.ρ S.Γ (rootCharHom a) i →
    CFSG.IsQuasisimple ↥K → Odd (Nat.card (Subgroup.center ↥K)) →
    B ≤ Subgroup.normalizer (K : Set X) →
    (∀ b ∈ B, ∃ a' ∈ S.D.torus, GGLiePartner G₀ η b a') →
    RCKFrameCover S a i h Mod →
    ∃ (M : LieUniversal) (P0 Pm0 : Subgroup (ModGL τ GGL))
      (D : PinnedReturnAt M (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
        K B (η.comp (Subgroup.inclusion hK)) P0 Pm0),
      Mod M (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ∧
        D.ClassicalAction

end CFSG.StandardType.RCKRP
