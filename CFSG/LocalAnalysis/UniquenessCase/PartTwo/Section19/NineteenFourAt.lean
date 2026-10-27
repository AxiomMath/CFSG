module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Gap19_4_innerAt (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L K : Subgroup G)
    (h : Ctx19_1 D V₀ V p L K) : Prop :=
  4 < mSub V₀ → R19_2At D V₀ V p L K h → R19_3At D V₀ V p L K h →
    normalizer (E3.wClos V₀ 2 D.T : Set G) ≤ D.M

theorem nineteen_four_At (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K) (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) (h66 : UC6.R6_6 D)
    (h861 : W3Lem86_1 G)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h2 : R19_2At D V₀ V p L K h) (h3 : R19_3At D V₀ V p L K h)
    (hgap : Gap19_4_innerAt D V₀ V p L K h) : R19_4At D V₀ V p L K h := by
  by_contra hm
  have hm' : 4 < mSub V₀ := by
    have : ¬ mSub V₀ ≤ 4 := hm
    omega
  exact normalizer_w_two_not_le D V₀ V p L K h h5_11 h5_13 h66 h861 hTim hcat hm'
    (hgap hm' h2 h3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
