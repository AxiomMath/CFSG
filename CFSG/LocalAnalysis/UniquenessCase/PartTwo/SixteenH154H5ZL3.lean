module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZRes
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZResGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W]

theorem s16h_H5_zcond_L3 [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t)
    (h : s16h_H5RowL3 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
    (hk : (∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
        ∃ g ∈ A ⊓ normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom) ∨
      commSub ⊤ L ∈ irrSet L) :
    s16h_H5ZCond A L := by
  have hk' : ∀ I₁ ∈ irrSet L, ∀ I₂ ∈ irrSet L,
      ∃ g ∈ A ⊓ normalizer (L : Set (MulAut W)), I₂ = I₁.map g.toMonoidHom := by
    rcases hk with hk | hk
    · exact hk
    · exact s16h_trans_of_commSub_mem_irrSet hc.comp.2.2 hk
  exact s16h_H5ZCond_of_autSub hc (s16h_H5_zcondGroup_of_world hc (s16h_L3World_of_row hc h hk'))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
