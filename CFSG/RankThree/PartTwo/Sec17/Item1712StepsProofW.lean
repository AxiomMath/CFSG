module

public import CFSG.RankThree.PartTwo.Sec17.Item17ClaimsProof

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late

@[expose] def Claim1719WNJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ Y₁ S : Subgroup G) (p : ℕ)
    (P : Subgroup G), Sec17Y1 G A c L Y₀ Y₁ S p P →
      IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∃ w ∈ Subgroup.normalizer (A : Set G) ⊓ Y₀,
        w ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
          w ∉ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G)

section Claim1719W

theorem claim1719W_of (h1715 : Item1715) (hNJ : Claim1719WNJ) : Claim1719W := by
  intro G _ _ A c L Y₀ Y₁ S p P h
  by_cases hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)
  · exact h.claim1719W_of_j2 h1715 hJ
  · exact hNJ G A c L Y₀ Y₁ S p P h (not_nonempty_iff.mp hJ)

end Claim1719W

end CFSG.RankThree.PartTwo.Sec17
