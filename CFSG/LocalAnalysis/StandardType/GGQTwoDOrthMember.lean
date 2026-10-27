module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMemberPair
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMemberPath
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthMemberFar
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitOrthA3

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.ClassicalInvolution.Phan CFSG.Open

@[expose] def QTwoOrthMemberFacts {G : Type} [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G) :
    Prop :=
  (∀ r ∈ ggAutomizer X Bs, GGIsReflection p r → ∀ r' ∈ ggAutomizer X Bs,
    GGIsReflection p r' → r * r' ≠ r' * r →
      UnitaryBlockStandardPair (GaloisField 2 2) 2 1 (ggRankTwoIn X Bs r r')
        (ggRankOneIn X Bs r) (ggRankOneIn X Bs r')) ∧
  (∀ r₁ ∈ ggAutomizer X Bs, GGIsReflection p r₁ → ∀ r₂ ∈ ggAutomizer X Bs,
    GGIsReflection p r₂ → ∀ r₃ ∈ ggAutomizer X Bs, GGIsReflection p r₃ →
      r₁ * r₂ ≠ r₂ * r₁ → r₂ * r₃ ≠ r₃ * r₂ → r₁ * r₃ = r₃ * r₁ → r₁ ≠ r₃ →
        ∃ θ : Su (GaloisField 2 2) 2 1 4 →* G,
          θ.range = ggRankTwoIn X Bs r₁ r₂ ⊔ ggRankTwoIn X Bs r₂ r₃) ∧
  (∀ r₁ ∈ ggAutomizer X Bs, GGIsReflection p r₁ → ∀ r₂ ∈ ggAutomizer X Bs,
    GGIsReflection p r₂ → ∀ r₃ ∈ ggAutomizer X Bs, GGIsReflection p r₃ →
    ∀ r₄ ∈ ggAutomizer X Bs, GGIsReflection p r₄ →
      r₁ * r₂ ≠ r₂ * r₁ → r₃ * r₄ ≠ r₄ * r₃ → r₁ * r₃ = r₃ * r₁ → r₁ * r₄ = r₄ * r₁ →
        r₂ * r₃ = r₃ * r₂ → r₂ * r₄ = r₄ * r₂ →
          ∀ x ∈ ggRankTwoIn X Bs r₁ r₂, ∀ y ∈ ggRankTwoIn X Bs r₃ r₄, x * y = y * x)

theorem qtwoOrthMemberFacts_of_frameCore {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs) (Φ : OrthFrameCore p Bs X)
    (hF : Nat.card Φ.F = 2) (hZ : Subgroup.center ↥X = ⊥) :
    QTwoOrthMemberFacts p Bs X := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr hrr r' hr' hrr' hnc
    exact qtwoOrth_standardPair Φ hF hZ hBs hr hr' hrr hrr' hnc
  · intro r₁ h₁ hr₁ r₂ h₂ hr₂ r₃ h₃ hr₃ h12 h23 h13 hne
    exact qtwoOrth_adjA3 Φ hF hZ hBs h₁ h₂ h₃ hr₁ hr₂ hr₃ h12 h23 h13 hne
  · intro r₁ h₁ hr₁ r₂ h₂ hr₂ r₃ h₃ hr₃ r₄ h₄ hr₄ h12 h34 h13 h14 h23 h24
    exact qtwoOrth_farEdgeEdge Φ hF hZ hBs h₁ h₂ h₃ h₄ hr₁ hr₂ hr₃ hr₄
      h12 h34 h13 h14 h23 h24

theorem qtwoOrthAdjA3_holds : QTwoOrthAdjA3Stmt := by
  intro G _ _ Bs Y hBs Φ hF h5 hZ r₁ h₁ hr₁ r₂ h₂ hr₂ r₃ h₃ hr₃ h12 h23 h13 hne
  exact qtwoOrth_adjA3 (p := 3) Φ hF hZ hBs h₁ h₂ h₃ hr₁ hr₂ hr₃ h12 h23 h13 hne

end CFSG.StandardType.QTwo

end
