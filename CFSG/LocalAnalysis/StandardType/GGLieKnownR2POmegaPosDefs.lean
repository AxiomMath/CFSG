module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos

namespace CFSG.StandardType.LieKnownR2.POmega

@[expose] def GGSixPOmegaPosExplicit
    (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X),
    CFSG.StandardType.ClassicalPosition.GGSixPosHyp t n f ψ p G₀ B₁ D J L x →
  ∃ (R Rm : Subgroup X),
        R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 t n f p ψ R Rm ∧
        ((∃ (t' : StatedLieTag) (mJ : ℕ) (βJ : Fin (ggU t' mJ f).D.rank → ℤ),
            (t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 3 ≤ mJ ∧
            βJ ∈ (ggU t' mJ f).D.roots ∧ GGLongRoot (ggU t' mJ f).D βJ ∧
            GGRootVia (ggU t' mJ f) J R βJ ∧
            ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
              CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
              Odd (Nat.card (Subgroup.center ↥K)) →
              ∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
                (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ mJ < mK ∧
                βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
                GGRootVia (ggU t'' mK f) K R βK) ∨
          (∃ (kJ : ℕ) (βJ : Fin (ggU .PSL (kJ + 1) f).D.rank → ℤ),
            βJ ∈ (ggU .PSL (kJ + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kJ + 1) f) J R βJ ∧
            ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
              CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
              Odd (Nat.card (Subgroup.center ↥K)) →
              (∃ (kK : ℕ) (βK : Fin (ggU .PSL (kK + 1) f).D.rank → ℤ), kJ < kK ∧
                βK ∈ (ggU .PSL (kK + 1) f).D.roots ∧ GGRootVia (ggU .PSL (kK + 1) f) K R βK) ∨
              (∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
                (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ 3 ≤ mK ∧ kJ + 1 ≤ mK ∧
                βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
                GGRootVia (ggU t'' mK f) K R βK)) ∨
          (∃ (m'J : ℕ) (βJ : Fin (ggU .PSU m'J f).D.rank → ℤ),
            βJ ∈ (ggU .PSU m'J f).D.roots ∧ GGRootVia (ggU .PSU m'J f) J R βJ ∧
            ∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ G₀ →
              CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
              Odd (Nat.card (Subgroup.center ↥K)) →
              (∃ (m'K : ℕ) (βK : Fin (ggU .PSU m'K f).D.rank → ℤ), m'J < m'K ∧
                βK ∈ (ggU .PSU m'K f).D.roots ∧ GGLongRoot (ggU .PSU m'K f).D βK ∧
                GGRootVia (ggU .PSU m'K f) K R βK) ∨
              (∃ (t'' : StatedLieTag) (mK : ℕ) (βK : Fin (ggU t'' mK f).D.rank → ℤ),
                (t'' = .POmegaPlus ∨ t'' = .POmegaMinus) ∧ 3 ≤ mK ∧ m'J ≤ mK ∧
                βK ∈ (ggU t'' mK f).D.roots ∧ GGLongRoot (ggU t'' mK f).D βK ∧
                GGRootVia (ggU t'' mK f) K R βK)))

end CFSG.StandardType.LieKnownR2.POmega

end
