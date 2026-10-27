module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalSuzuki
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.ModelsSymplectic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

@[expose] def Asch58Parabolic (t : StatedLieTag) (n f : ℕ) : Prop :=
  f = 1 ∧ t ≠ .trialityD4 ∨
    f = 2 ∧ (t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨
      t = .E8 ∨ t = .PSU ∧ n = 3)

@[expose] def Asch58UnitaryFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), n = 6 ∨ n = 7 →
    CFSG.Models.LieModel X .PSU n 2 2 →
    3 < CFSG.Open.pRank 5 (⊤ : Subgroup X) ∧
      ∀ S : Sylow 2 X, 1 < CFSG.Open.pRank 5 (Subgroup.normalizer ((S : Subgroup X) : Set X))

end CFSG.LocalAnalysis.WeakClosure81
