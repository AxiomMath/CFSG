module

public import CFSG.RankThree.PartTwo.Sec16.Item166ResProofTwoPow

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank

@[expose] def Step166OmegaOther : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ¬ IsL3TwoPow L →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Omega166 A Y₀

@[expose] def Step166CtrOther : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ¬ IsL3TwoPow L →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Ctr166 A Y₀

theorem step166OmegaNot2n_of (hHJ : Step166OmegaHJ) (hOther : Step166OmegaOther) :
    Step166OmegaNot2n := by
  intro G _ _ A c L Y₀ hs hL
  by_cases hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  · exact hHJ G A c L Y₀ hs hJ
  · exact hOther G A c L Y₀ hs hL (not_nonempty_iff.mp hJ)

theorem step166CtrNot2n_of (hHJ : Step166CtrHJ) (hOther : Step166CtrOther) :
    Step166CtrNot2n := by
  intro G _ _ A c L Y₀ hs hL
  by_cases hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  · exact hHJ G A c L Y₀ hs hJ
  · exact hOther G A c L Y₀ hs hL (not_nonempty_iff.mp hJ)

end CFSG.RankThree.PartTwo.Sec16

