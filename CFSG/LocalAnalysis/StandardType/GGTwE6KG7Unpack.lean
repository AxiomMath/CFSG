module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.LocalAnalysis.StandardType.GGMarkingAllInduces
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreDefs

public section

namespace CFSG.StandardType.TwE6KG7

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent
  CFSG.StandardType.SCFourCover

theorem exists_recipe_of_marking {X : Type} [Group X] {A : Subgroup (MulAut X)}
    (h : LargeEvenMarking X (fun lab _ _ I _ θ =>
      lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1 ∧ GGInducedInn A θ I)) :
    ∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ n ∧ 3 ∣ 2 ^ n + 1 ∧
      Nat.card K = (2 ^ n) ^ 2 ∧
      ∃ θ : X ⧸ Subgroup.center X ≃* TwE6Delta.RecipeR K n,
        ∀ a ∈ A, ggInducedAut θ a ∈ TwE6Delta.RecipeI K n := by
  obtain ⟨-, lab, hlab, hraw⟩ := h
  have htag : lab.tag = .twE6 := by
    obtain ⟨R, _, I, F, -, -, θ, hθ⟩ := largeEvenRawDatum_exists hraw
    exact hθ.1
  rcases lab with ⟨t, l, n⟩
  change t = .twE6 at htag
  subst htag
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwisted] at hraw
  obtain ⟨K, hK, hfin, hcard, hq⟩ := hraw
  obtain ⟨-, -, θ, hθ⟩ := hq
  exact ⟨n, K, hK, hfin, hlab.1, hθ.2.1, hcard, θ, hθ.2.2⟩

end CFSG.StandardType.TwE6KG7
