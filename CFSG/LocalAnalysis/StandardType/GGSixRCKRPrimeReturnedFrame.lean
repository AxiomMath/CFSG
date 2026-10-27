module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnAssembly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleCycle

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)

@[expose] noncomputable def rckRootVal {τ : Tag} (t : ModGL τ GGL) (γ : Fin τ.rank → ℤ) : GGLˣ :=
  rootCharHom (rckTorusCoord t) (Multiplicative.ofAdd γ)

@[expose] def RCKReturnedCover
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (h : ℕ) (Mod : LieUniversal → ℕ → Prop) : Prop :=
  ∃ (M : LieUniversal) (φ : M.K →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (τK : Tag) (SK : LangSetup τK GGL 5)
    (κ : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →* ModGL τK GGL)
    (ι : (Fin τ.rank → ℤ) → (Fin τK.rank → ℤ)),
    Mod M (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ∧
    StandardReturnAt M (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ∧
    Function.Surjective φ ∧ φ.ker ≤ Subgroup.center M.K ∧
    Finite M.K ∧ Group.IsPerfect M.K ∧ CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit M.K ∧
    (∃ β ∈ M.D.roots, GGLongRoot M.D β ∧ ∃ γ₀ : Fin τK.rank → ℤ, IsRoot τK γ₀ ∧
      ∃ z₀ ∈ adjointGroup τK GGL,
        ((rootSubgroup τK GGL γ₀).map (MulAut.conj z₀).toMonoidHom).map SK.D.step =
            (rootSubgroup τK GGL γ₀).map (MulAut.conj z₀).toMonoidHom ∧
        ((rootSubgroup τK GGL (-γ₀)).map (MulAut.conj z₀).toMonoidHom).map SK.D.step =
            (rootSubgroup τK GGL (-γ₀)).map (MulAut.conj z₀).toMonoidHom ∧
        (M.D.rootGroup β).map (κ.comp φ) =
          (rootSubgroup τK GGL γ₀).map (MulAut.conj z₀).toMonoidHom ⊓
            SK.D.step.eqLocus (MonoidHom.id _) ∧
        (M.D.rootGroup (-β)).map (κ.comp φ) =
          (rootSubgroup τK GGL (-γ₀)).map (MulAut.conj z₀).toMonoidHom ⊓
            SK.D.step.eqLocus (MonoidHom.id _)) ∧
    (∀ b ∈ S.D.torus,
      GGPsiInnerDiag M.D ((rationalComponent S.ρ S.Γ (rootCharHom a) i).subtype.comp φ) b) ∧
    (τK = Tag.D4 ∨ τK = Tag.E6 ∨ τK = Tag.E7) ∧
    SK.D.q = 2 ^ (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ∧
    κ.ker = Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
    κ.range = SK.Γ ∧
    Set.BijOn ι (componentRoots (rootCharHom a) i) {γ' | IsRoot τK γ'} ∧
    (∀ γ ∈ componentRoots (rootCharHom a) i, ι (-γ) = -ι γ) ∧
    (∀ γ ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
      CFSG.LieType.Steinberg.Adjoint.iform (ι γ) (ι δ) = CFSG.LieType.Steinberg.Adjoint.iform γ δ) ∧
    (∀ γ ∈ componentRoots (rootCharHom a) i,
      ι ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)]
        γ) = (SK.ρ : (Fin τK.rank → ℤ) → _) (ι γ)) ∧
    ∀ b ∈ S.D.torus, ∃ t ∈ SK.D.torus,
      (∀ (x : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        (hx : b * (x : ModGL τ GGL) * b⁻¹ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i),
        κ ⟨b * (x : ModGL τ GGL) * b⁻¹, hx⟩ = t * κ x * t⁻¹) ∧
      ∀ γ ∈ componentRoots (rootCharHom a) i, rckRootVal t (ι γ) = rckRootVal b γ

@[expose] def RCKCarrierRet
    : Prop :=
  ∀ (τ : Tag) (S : LangSetup τ GGL 5) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ),
    S.D.q = 2 ^ h →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKNonclassShape S.ρ (componentRoots (rootCharHom a) i) →
    RCKReturnedCover S a i h
      (fun M g =>
        (compRank (componentRoots (rootCharHom a) i) = 6 ∧
          ((twistKind S.ρ (rootCharHom a) i = .inner ∧ M = ggU .E6 0 g) ∨
            (twistKind S.ρ (rootCharHom a) i = .exc ∧ M = ggU .twistedE6 0 g))) ∨
        (compRank (componentRoots (rootCharHom a) i) = 7 ∧ M = ggU .E7 0 g) ∨
        (compRank (componentRoots (rootCharHom a) i) = 4 ∧
          ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
            TriField F σ g ∧ M = triD4Universal F σ))

@[expose] def RCKFrameIncidence
    : Prop :=
  ∀ (τ : Tag), (τ = Tag.D4 ∨ τ = Tag.E6 ∨ τ = Tag.E7) → ∀ (S : LangSetup τ GGL 5)
    (γ γ' : Fin τ.rank → ℤ), IsRoot τ γ → IsRoot τ γ' →
    ∀ z ∈ adjointGroup τ GGL, ∀ z' ∈ adjointGroup τ GGL,
    ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom →
    ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom →
    ((rootSubgroup τ GGL γ').map (MulAut.conj z').toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL γ').map (MulAut.conj z').toMonoidHom →
    ((rootSubgroup τ GGL (-γ')).map (MulAut.conj z').toMonoidHom).map S.D.step =
        (rootSubgroup τ GGL (-γ')).map (MulAut.conj z').toMonoidHom →
    ∃ k ∈ S.Γ,
      (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ⊓
          S.D.step.eqLocus (MonoidHom.id _) =
        ((rootSubgroup τ GGL γ').map (MulAut.conj z').toMonoidHom ⊓
          S.D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj k).toMonoidHom ∧
      (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom ⊓
          S.D.step.eqLocus (MonoidHom.id _) =
        ((rootSubgroup τ GGL (-γ')).map (MulAut.conj z').toMonoidHom ⊓
          S.D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj k).toMonoidHom

@[expose] def RCKADEShape {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* GGLˣ) (i : KernelComponent χ) : Prop :=
  compRank (componentRoots χ i) = 1 ∨
    (twistKind ρ χ i = .inner ∧ 2 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) + 1)) ∨
    twistKind ρ χ i = .suN ∨
    (twistKind ρ χ i = .inner ∧ 4 ≤ compRank (componentRoots χ i) ∧
      (componentRoots χ i).ncard = 2 * compRank (componentRoots χ i) *
        (compRank (componentRoots χ i) - 1)) ∨
    twistKind ρ χ i = .twoD ∨
    (twistKind ρ χ i = .inner ∧
      ((compRank (componentRoots χ i) = 6 ∧ (componentRoots χ i).ncard = 72) ∨
        (compRank (componentRoots χ i) = 7 ∧ (componentRoots χ i).ncard = 126) ∨
        (compRank (componentRoots χ i) = 8 ∧ (componentRoots χ i).ncard = 240))) ∨
    twistKind ρ χ i = .exc

@[expose] def RCKADEModel
    (M : LieUniversal) (g : ℕ) : Prop :=
  (∃ (t : StatedLieTag) (n : ℕ),
      (t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨
        t = .twistedE6) ∧ CFSG.Open.StatedLieAdmissible t n 2 g ∧ M = ggU t n g) ∨
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F), TriField F σ g ∧
      M = triD4Universal F σ

@[expose] def RCKFrameCoverPair
    {τ : Tag} {p₀ : ℕ} (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) (h : ℕ) (Mod : LieUniversal → ℕ → Prop) : Prop :=
  ∃ (M : LieUniversal) (φ : M.K →* ModGL τ GGL),
    Mod M (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ∧
    RCKADEModel M (h * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) ∧
    φ.range = rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
    φ.ker ≤ Subgroup.center M.K ∧
    Finite M.K ∧ Group.IsPerfect M.K ∧ CFSG.SeitzReduction.UnitaryPilot.OddCentralSplit M.K ∧
    (componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 →
      ∀ β ∈ M.D.roots, GGLongRoot M.D β → ∃ γ ∈ componentRoots (rootCharHom a) i,
        ∃ z ∈ torusGroup τ GGL ⊔ rootSpan τ GGL (kernelRoots (rootCharHom a)),
        ((rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom).map S.D.step =
            (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ∧
        ((rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom).map S.D.step =
            (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom ∧
        (M.D.rootGroup β).map φ = (rootSubgroup τ GGL γ).map (MulAut.conj z).toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _) ∧
        (M.D.rootGroup (-β)).map φ = (rootSubgroup τ GGL (-γ)).map (MulAut.conj z).toMonoidHom ⊓
            S.D.step.eqLocus (MonoidHom.id _))

@[expose] def RCKCarrierPairADE
    : Prop :=
  ∀ (τ : Tag) (p₀ : ℕ) (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ),
    rootDiagUnit τ a ∈ S.D.torus →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → rootDiagUnit τ a ^ p = 1 →
    ∀ (i : KernelComponent (rootCharHom a)) (h : ℕ),
    S.D.q = 2 ^ h → RCKADEShape S.ρ (rootCharHom a) i →
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
    RCKFrameCoverPair S a i h
      (fun M g =>
        (compRank (componentRoots (rootCharHom a) i) = 1 ∧ M = ggU .PSL 2 g) ∨
        (twistKind S.ρ (rootCharHom a) i = .inner ∧
          2 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard =
            compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) + 1) ∧
          M = ggU .PSL (compRank (componentRoots (rootCharHom a) i) + 1) g) ∨
        (twistKind S.ρ (rootCharHom a) i = .suN ∧
          M = ggU .PSU (compRank (componentRoots (rootCharHom a) i) + 1) g) ∨
        (twistKind S.ρ (rootCharHom a) i = .inner ∧
          4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard =
            2 * compRank (componentRoots (rootCharHom a) i) *
              (compRank (componentRoots (rootCharHom a) i) - 1) ∧
          M = ggU .POmegaPlus (compRank (componentRoots (rootCharHom a) i)) g) ∨
        (twistKind S.ρ (rootCharHom a) i = .twoD ∧
          M = ggU .POmegaMinus (compRank (componentRoots (rootCharHom a) i)) g) ∨
        (twistKind S.ρ (rootCharHom a) i = .inner ∧
          ((compRank (componentRoots (rootCharHom a) i) = 6 ∧
              (componentRoots (rootCharHom a) i).ncard = 72 ∧ M = ggU .E6 0 g) ∨
            (compRank (componentRoots (rootCharHom a) i) = 7 ∧
              (componentRoots (rootCharHom a) i).ncard = 126 ∧ M = ggU .E7 0 g) ∨
            (compRank (componentRoots (rootCharHom a) i) = 8 ∧
              (componentRoots (rootCharHom a) i).ncard = 240 ∧ M = ggU .E8 0 g))) ∨
        (twistKind S.ρ (rootCharHom a) i = .exc ∧
          ((compRank (componentRoots (rootCharHom a) i) = 6 ∧ M = ggU .twistedE6 0 g) ∨
            (compRank (componentRoots (rootCharHom a) i) = 4 ∧
              ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F),
                TriField F σ g ∧ M = triD4Universal F σ))))

@[expose] def RCKStdEnvelope
    : Prop :=
  ∀ (τ : Tag), (τ = Tag.D4 ∨ τ = Tag.E6 ∨ τ = Tag.E7 ∨ τ = Tag.E8) → ∀ (S : LangSetup τ GGL 5),
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (a : Fin τ.rank → GGLˣ),
      rootDiagUnit τ a ∈ S.D.torus → rootDiagUnit τ a ≠ 1 → (∀ j, a j ^ p = 1) →
      ∀ i : KernelComponent (rootCharHom a),
        CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RCKADEShape S.ρ (rootCharHom a) i

end CFSG.StandardType.RCKRP
