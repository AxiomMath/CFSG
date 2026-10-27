module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.UniquenessCase.UCKU3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

@[expose] def R891GammaA7 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsAlt X 7 → ∀ E : Subgroup X, IsElemAbelian 3 E →
    Nat.card E = 9 → rankThreeGamma 1 3 E = ⊤

@[expose] def R891GammaM22 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSpor X .M22 → ∀ E : Subgroup X, IsElemAbelian 3 E →
    Nat.card E = 9 → rankThreeGamma 1 3 E = ⊤

@[expose] def R891GammaL3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p ^ f % 3 = 1 → p ^ f ≠ 4 →
    LieModel X .PSL 3 p f → ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E = 9 →
      rankThreeGamma 1 3 E = ⊤

@[expose] def R891GammaU3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p ^ f % 3 = 2 → LieModel X .PSU 3 p f →
    ∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E = 9 → rankThreeGamma 1 3 E = ⊤

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
