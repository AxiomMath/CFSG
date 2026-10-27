module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeTableZDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUStd
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAut
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.PlanesSetup
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.RankThree.PartOne.KE.E7FiveBlock

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

open CFSG.HardMathSupport.Timmesfeld.CrossChar in
theorem tableZ_recipe_catalogue
    {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (σ' : K' ≃+* K'),
      Nat.card K' = (2 ^ n) ^ 2 ∧ (∀ c, σ' c = c ^ (2 ^ n)) ∧
      ∃ e : LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n) ≃*
          ↥(twistedE6RootGroup K' σ'),
        ∀ α ∈ LargeEvenChevIDImage (LargeEvenCartanE 6) K
            (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n),
          MulAut.congr e α ∈
            CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived ↥(twistedE6RootGroup K' σ') := by
  obtain ⟨σ, hσ, ε, -⟩ :=
    CFSG.StandardType.TwE6Transport.exists_recipeConj (K := K) hn hK
  refine ⟨K, inferInstance, inferInstance, σ, hK, hσ, ε.symm, ?_⟩
  intro α hα
  have hEq : CFSG.StandardType.GGInndiagCommEq
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))
      (LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K
        (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) :=
    CFSG.StandardType.InndiagCommRest.ggInndiagCommEq_twE6 hn K hK
  have hmem : α ∈ CFSG.StandardType.ggInndiag
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n))
      (LargeEvenChevIDImage (LargeEvenCartanE 6) K
        (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) :=
    CFSG.StandardType.subset_ggInndiag hα
  have hβ : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) := by
    have hmem2 : α ∈ CFSG.StandardType.ggInndiagComm
        (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) := by
      rw [← hEq]; exact hmem
    rwa [CFSG.StandardType.ggInndiagComm_eq_innAutDerived] at hmem2
  exact (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr ε.symm).2 hβ

end CFSG.StandardType.TablePThreeKG

end
