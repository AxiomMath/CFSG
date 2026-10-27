module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LieType.Steinberg.TwistedD4.Defs

public section

namespace CFSG.StandardType.S2MathFi1035Pos

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

@[expose] def GGRootVia {X : Type} [Group X] (M : LieUniversal) (K R : Subgroup X)
    (β : Fin M.D.rank → ℤ) : Prop :=
  ∃ φ : M.K →* X, φ.range = K ∧ φ.ker ≤ Subgroup.center M.K ∧ ∃ u : M.K,
    R = ggRootSub M.D φ β u

@[expose] def GGRootPairVia {X : Type} [Group X] (M : LieUniversal) (H R Rm : Subgroup X)
    (β : Fin M.D.rank → ℤ) : Prop :=
  ∃ φ : M.K →* X, φ.range = H ∧ φ.ker ≤ Subgroup.center M.K ∧ ∃ u : M.K,
    R = ggRootSub M.D φ β u ∧ Rm = ggRootSub M.D φ (-β) u

@[expose] def GGPosTag (t : StatedLieTag) : Prop :=
  t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .F4 ∨ t = .E6 ∨
    t = .E7 ∨ t = .E8 ∨ t = .twistedE6

@[expose] def GGShortTag (t : StatedLieTag) : Prop :=
  t = .PSp ∨ t = .F4 ∨ GGTwistedTag t

@[expose] noncomputable def triD4Universal
    (F : Type) [Field F] (σ : F →+* F) : LieUniversal :=
  ⟨↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup σ),
    CFSG.LieType.Steinberg.TwistedD4.twistedDatum σ⟩

@[expose] def TriField (F : Type) [Field F] (σ : F →+* F) (g : ℕ) : Prop :=
  1 ≤ g ∧ Nat.card F = (2 ^ g) ^ 3 ∧ ∀ c : F, σ c = c ^ (2 ^ g)

@[expose] def GGRootPosJ {X : Type} [Group X]
    (J R Rm : Subgroup X) : Prop :=
  (∃ (t' : StatedLieTag) (m g : ℕ) (β : Fin (ggU t' m g).D.rank → ℤ), GGPosTag t' ∧ 1 ≤ g ∧
      GGLongRoot (ggU t' m g).D β ∧ GGRootPairVia (ggU t' m g) J R Rm β) ∨
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F) (g : ℕ)
      (β : Fin (triD4Universal F σ).D.rank → ℤ), TriField F σ g ∧
        GGLongRoot (triD4Universal F σ).D β ∧ GGRootPairVia (triD4Universal F σ) J R Rm β

@[expose] def GGRootPosNbr {X : Type} [Group X]
    (K R : Subgroup X) : Prop :=
  (∃ (t' : StatedLieTag) (m g : ℕ) (β : Fin (ggU t' m g).D.rank → ℤ), GGPosTag t' ∧ 1 ≤ g ∧
      β ∈ (ggU t' m g).D.roots ∧
        (GGLongRoot (ggU t' m g).D β ∨ (GGShortTag t' ∧ 2 • β ∉ (ggU t' m g).D.roots)) ∧
        GGRootVia (ggU t' m g) K R β) ∨
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F) (g : ℕ)
      (β : Fin (triD4Universal F σ).D.rank → ℤ), TriField F σ g ∧
        GGLongRoot (triD4Universal F σ).D β ∧ GGRootVia (triD4Universal F σ) K R β

@[expose] def GGRootPosG0 {X : Type} [Group X]
    (t : StatedLieTag) (n f p : ℕ) (ψ : (ggU t n f).K →* X)
    (R Rm : Subgroup X) : Prop :=
  ∃ β : Fin (ggU t n f).D.rank → ℤ, β ∈ (ggU t n f).D.roots ∧
    (GGLongRoot (ggU t n f).D β ∨
      ((t = .PSp ∨ t = .F4 ∨ ((t = .PSU ∨ t = .twistedE6) ∧ p ∣ 2 ^ f - 1)) ∧
        2 • β ∉ (ggU t n f).D.roots)) ∧
    ∃ u : (ggU t n f).K, R = ggRootSub (ggU t n f).D ψ β u ∧
      Rm = ggRootSub (ggU t n f).D ψ (-β) u

end CFSG.StandardType.S2MathFi1035Pos
