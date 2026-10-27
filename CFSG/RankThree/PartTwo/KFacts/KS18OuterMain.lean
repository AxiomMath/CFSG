module

public import CFSG.RankThree.PartTwo.KFacts.KS18OuterZ3
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeis

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS18

theorem ks18OuterInvolution : KS18OuterInvolution := by
  intro Y _ _ X t E hO hX hXiso htX hYt ht2 hEX hE hE27 hEt hB
  rcases hXiso with he | hXH
  · obtain ⟨e⟩ := he
    have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact hE.2 _ x.2)⟩
    exact outer_involution_Z3 L34.card_galoisField_two_two hO
      (e.trans (MulEquiv.prodCongr (MulEquiv.refl _) (L34.projSLEquivProjectiveSL 3 _))) hX htX
      hYt ht2 hEX hE3 hE27 hEt
  · exact outer_involution_heis hO hX hXH htX hYt ht2 hEX hE hE27 hEt hB

end CFSG.RankThree.PartTwo.KFacts.KS18
