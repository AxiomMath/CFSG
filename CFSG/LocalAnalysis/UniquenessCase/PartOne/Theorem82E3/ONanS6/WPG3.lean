module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open scoped commutatorElement Pointwise
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem alpha_const_of_local'' (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hlocal : ∀ A : Subgroup G, CFSG.Open.IsElemAbelian 3 A → Nat.card A = 27 →
      zSub P c.L ≤ A → A ≤ P ⊓ c.L →
      ∀ E ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.hyperplanes 3 A,
        ∀ E' ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.hyperplanes 3 A,
          thetaAlpha 3 E = thetaAlpha 3 E') :
    ∀ E E' : Subgroup G, E ≤ P → E' ≤ P → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E = 9 → CFSG.Open.IsElemAbelian 3 E' → Nat.card E' = 9 →
        thetaAlpha 3 E = thetaAlpha 3 E' := by
  exact alpha_const_of_local' (P := P) c hON hP hlocal

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
