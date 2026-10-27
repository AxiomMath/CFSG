module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AABBAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AABAAB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin Subgroup

variable {W : Type} [CommGroup W]

theorem s16h_e3_CycTwoP3M4AA2AABBAA_normal_e9
    [Finite W] [Finite (MulAut W)]
    (hexp : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 4)
    {A : Subgroup (MulAut W)} {z : MulAut W}
    (hzA : z ∈ A) (hzord : orderOf z = 3)
    (hfpf : ∀ w : W, z w = w → w = 1)
    (hAn : A ≤ Subgroup.normalizer (Subgroup.zpowers z : Set (MulAut W)))
    (hline : ∃ w : W, w ≠ 1 ∧ ∀ b ∈ A, b ≠ 1 → orderOf b = 3 → b w = w →
      b ∈ Subgroup.zpowers z)
    (h2 : 2 ≤ CFSG.Open.pRank 3 A) :
    ∃ D : Subgroup (MulAut W),
      D ≤ A ∧ IsElemAbelianOfRank 3 2 ↥D ∧ (D.subgroupOf A).Normal ∧
      Subgroup.zpowers z ≤ D := by
  obtain ⟨E, hEA, hE⟩ :=
    s16h_e3_CycTwoP3M4AA2AABAAA_exists_elemAbelian hexp hcard h2
  have hEnorm := s16h_e3_CycTwoP3M4AA2AABAAB_normal_of_elemAbelian hexp hcard hzA hzord
    hfpf hAn hline hEA hE
  exact ⟨E, hEA, hE, hEnorm,
    s16h_e3_CycTwoP3M4AA2AABBAAA_zpowers_le_of_normal hexp hcard hzord hzA hEA hE hEnorm⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
