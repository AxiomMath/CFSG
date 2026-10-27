module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

@[expose] def GGThmSRangeAt {X : Type} [Group X]
    (K R : Subgroup X) : Prop :=
  (∃ (m g : ℕ) (β : Fin (ggU .PSL (m + 1) g).D.rank → ℤ),
      ((g = 1 ∧ 4 ≤ m) ∨ (2 ≤ g ∧ 3 ≤ m) ∨ (3 ≤ g ∧ 2 ≤ m)) ∧
      β ∈ (ggU .PSL (m + 1) g).D.roots ∧ GGRootVia (ggU .PSL (m + 1) g) K R β) ∨
  (∃ (n g : ℕ) (β : Fin (ggU .PSU n g).D.rank → ℤ), 3 ≤ n ∧ ¬ (n = 3 ∧ g = 1) ∧
      β ∈ (ggU .PSU n g).D.roots ∧
      (GGLongRoot (ggU .PSU n g).D β ∨ (6 ≤ n ∧ 2 ≤ g ∧ 2 • β ∉ (ggU .PSU n g).D.roots)) ∧
      GGRootVia (ggU .PSU n g) K R β) ∨
  (∃ (n g : ℕ) (β : Fin (ggU .PSp n g).D.rank → ℤ), StatedLieAdmissible .PSp n 2 g ∧
      β ∈ (ggU .PSp n g).D.roots ∧ GGRootVia (ggU .PSp n g) K R β) ∨
  (∃ (n g : ℕ) (β : Fin (ggU .POmegaPlus n g).D.rank → ℤ), 4 ≤ n ∧
      β ∈ (ggU .POmegaPlus n g).D.roots ∧ GGRootVia (ggU .POmegaPlus n g) K R β) ∨
  (∃ (n g : ℕ) (β : Fin (ggU .POmegaMinus n g).D.rank → ℤ), 4 ≤ n ∧
      β ∈ (ggU .POmegaMinus n g).D.roots ∧ GGLongRoot (ggU .POmegaMinus n g).D β ∧
      GGRootVia (ggU .POmegaMinus n g) K R β) ∨
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F) (g : ℕ)
      (β : Fin (triD4Universal F σ).D.rank → ℤ), TriField F σ g ∧
      GGLongRoot (triD4Universal F σ).D β ∧ GGRootVia (triD4Universal F σ) K R β) ∨
  (∃ (t : StatedLieTag) (g : ℕ) (β : Fin (ggU t 0 g).D.rank → ℤ),
      (t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ 1 ≤ g ∧
      β ∈ (ggU t 0 g).D.roots ∧ GGRootVia (ggU t 0 g) K R β) ∨
  ∃ (g : ℕ) (β : Fin (ggU .twistedE6 0 g).D.rank → ℤ), β ∈ (ggU .twistedE6 0 g).D.roots ∧
    ((1 ≤ g ∧ GGLongRoot (ggU .twistedE6 0 g).D β) ∨
      (2 ≤ g ∧ ¬ GGLongRoot (ggU .twistedE6 0 g).D β)) ∧
    GGRootVia (ggU .twistedE6 0 g) K R β

@[expose] def GGSixExcPosExplicit
    (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X),
    GGSixPosHyp t n f ψ p G₀ B₁ D J L x →
    ∃ R Rm : Subgroup X, R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 t n f p ψ R Rm ∧
      ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
        CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
        Odd (Nat.card (Subgroup.center ↥K)) → K = G₀ ∨ GGThmSRangeAt K R

end CFSG.StandardType.LieKnownR2
