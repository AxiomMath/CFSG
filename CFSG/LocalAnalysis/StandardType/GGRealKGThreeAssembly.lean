module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeSplit
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeLin
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeNs
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeU63
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeSmall
public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootSL2
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6Split
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeExcSplit
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeE6Nonsplit
import CFSG.LocalAnalysis.StandardType.GGRealKGExcNegRows
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeF4Nonsplit
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGTwE6HyperplaneFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRealKGThreeRow_twe6Nonsplit_of_recipe_rootSL2
    (h : ∀ (n : ℕ), 2 ≤ n → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = (2 ^ n) ^ 2 → 3 ∣ 2 ^ n + 1 →
        GGTorusRootSL2 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)) :
    GGRealKGThreeRow .twe6Nonsplit := by
  intro p lab hp hlab hl hs
  obtain ⟨hp3, ⟨htag, h3⟩, -⟩ := hs
  subst hp3
  refine TwE6Delta.labelAll htag ?_
  intro K _ _ hK
  exact ⟨4, ggTorusLift_twE6Three hlab.1 hK h3, h lab.n hl.2.1 K hK h3⟩



theorem ggReflRealizedQFourInputThree_of_open (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hT6n : GGRealKGThreeRow .twe6Nonsplit) :
    GGReflRealizedQFourInputThree := by
  refine ggReflRealizedQFourInputThree_of_rootSL2On_U63 hLB hSP
    (ggRealRootSL2On_three_offU63_of_rows fun i hi => ?_)
  cases i
  case aSplit => exact ggRealKGThreeRow_aSplit
  case aSplitDvd => exact ggRealKGThreeRow_aSplitDvd
  case aNonsplit => exact ggRealKGThreeRow_aNonsplit
  case aNonsplitDvd => exact ggRealKGThreeRow_aNonsplitDvd
  case uSplit => exact ggRealKGThreeRow_uSplit
  case uSplitDvd => exact ggRealKGThreeRow_uSplitDvd
  case uNonsplit => exact ggRealKGThreeRow_uNonsplit
  case uNonsplitDvd => exact (hi rfl).elim
  case spSplit => exact ggRealKGThreeRow_spSplit
  case spNonsplit => exact ggRealKGThreeRow_spNonsplit
  case dSplit => exact ggRealKGThreeRow_dSplit
  case dNonsplit => exact ggRealKGThreeRow_dNonsplit
  case twdSplit => exact ggRealKGThreeRow_twdSplit_of_uSplit ggRealKGThreeRow_uSplit
  case twdNonsplit => exact ggRealKGThreeRow_twdNonsplit
  case e6Split => exact ggRealKGThreeRow_e6Split
  case e6Nonsplit => exact ggRealKGThreeRow_e6Nonsplit
  case e7Split => exact ggRealKGThreeRow_e7Split
  case e7Nonsplit => exact ggRealKGThreeRow_e7Nonsplit
  case e8Split => exact ggRealKGThreeRow_e8Split
  case e8Nonsplit => exact ggRealKGThreeRow_e8Nonsplit
  case f4Split => exact ggRealKGThreeRow_f4Split
  case f4Nonsplit => exact ggRealKGThreeRow_f4Nonsplit
  case twe6Split => exact ggRealKGThreeRow_twe6Split
  case twe6Nonsplit => exact hT6n
  case small => exact ggRealKGThreeRow_small

section RationalComponentRow

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Lang.E6Descent CFSG.ComponentClassification.CatalogueBPrimeJoin
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem ggRealKGThreeRow_twe6Nonsplit_of_jgeom : GGRealKGThreeRow .twe6Nonsplit := by
  apply ggRealKGThreeRow_twe6Nonsplit_of_recipe_rootSL2
  intro n hn K _ _ hK h3
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn2 : n = 2 := by omega
    rw [hn2] at h3
    norm_num at h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * n)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm])
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let σ := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  let Fr := iterateFrobenius (AlgebraicClosure K) 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => by rw [iterateFrobenius_def]
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn1 hK σ hσ
  exact TwE6ThreeRootGen.ggTorusRootSL2_recipeR_twE6Three_of_jgeom hn1 hn hK σ hσ Fr hFr ε hε h3
    (by
      intro L' _ _ ψ A hTB hnt g hg hφ hg2
      obtain ⟨m, hgm⟩ := hg2
      exact TwE6HyperplaneFrame.isQuasisimple_jgeom_of_tableB hn1 hK σ hσ Fr hFr ε hε
        hn3 hTB hnt hg hφ hgm)

theorem ggReflRealizedQFourInputThree_of_jgeom (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) :
    GGReflRealizedQFourInputThree :=
  ggReflRealizedQFourInputThree_of_open hLB hSP ggRealKGThreeRow_twe6Nonsplit_of_jgeom

end RationalComponentRow

end CFSG.StandardType

end
