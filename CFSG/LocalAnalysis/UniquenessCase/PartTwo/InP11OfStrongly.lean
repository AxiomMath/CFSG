module

public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UCFront11
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inP11_of_strongly {D : Data G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    {X : Subgroup G} (hXM : X ≤ D.M) (hXp : IsPGroup p ↥X) (hXexp : ∀ x ∈ X, x ^ p = 1)
    (hXnc : ¬ IsCyclic ↥X) (hperm : Permutes X D.T) :
    F11.InP11 D X :=
  ⟨p, hp, hp2, hXM, hXp, hXexp, hXnc, hperm,
    hstr.rankThreeGamma_one_le_of_le hp hXp hXM, Or.inl hstr⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
