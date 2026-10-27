module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8100R
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNineAxB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.WeakClosure81.SixFifteen
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap17_45_NonabChief (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l r : ℕ) (C Dc : Subgroup G) (Gamma : Set G) (x : G)
    (A₀ A B : Subgroup G),
    V₀ ≠ ⊥ → Ctx17_42 D V₀ V L X p n l C Dc Gamma →
    F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X →
    F08.Case8100FourR D ![L, conjSubgroup L x] p X →
    CFSG.ABGLocalTools.IsSylowOf r A X → Permutes A D.T → B ≤ D.M →
    Nat.card B = p → ⁅A, B⁆ = A → Permutes B D.T →
    centralizer (D.Z : Set G) ≤ D.M →
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M → F08.R8101R D →
    ∀ N H R : Subgroup G, N ∈ calMOf (A ⊔ B ⊔ D.T) → N ≠ D.M →
      A ⊔ B ⊔ D.T ≤ H → H ≤ N → ¬ H ≤ D.M →
      (∀ H' : Subgroup G, A ⊔ B ⊔ D.T ≤ H' → H' ≤ H → ¬ H' ≤ D.M → H' = H) →
      kerM D.M H < R → R ≤ H → H ≤ normalizer (R : Set G) →
      (∀ W : Subgroup G, kerM D.M H ≤ W → W ≤ R → H ≤ normalizer (W : Set G) →
        W = kerM D.M H ∨ W = R) →
      ¬ ⁅R, R⁆ ≤ kerM D.M H → False

@[expose] def Gap17_45_UniqueMaxFiveSE (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (L X : Subgroup G) (p n l r : ℕ) (C Dc : Subgroup G) (Gamma : Set G) (x : G)
    (A₀ A B : Subgroup G),
    V₀ ≠ ⊥ → Ctx17_42 D V₀ V L X p n l C Dc Gamma →
    F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X →
    F08.Case8100FourR D ![L, conjSubgroup L x] p X →
    CFSG.ABGLocalTools.IsSylowOf r A X → Permutes A D.T → B ≤ D.M →
    Nat.card B = p → ⁅A, B⁆ = A → Permutes B D.T →
    centralizer (D.Z : Set G) ≤ D.M →
    CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M → F08.R8101R D →
    UniqueMax D.M (A ⊔ B ⊔ D.T)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
