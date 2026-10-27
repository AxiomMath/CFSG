module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyNine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s17_false_of_rk_barSub_add_lt (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Gt2 G)
    (h183 : W3Thm183 G) (h161 : W16One G)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) (h0 : V₀ ≠ ⊥)
    (hm2 : 2 < mBar D.M V₀ V hV.isElemAbelian)
    (hrk : ∀ g : G, g ∉ D.M → conjSubgroup V g ≤ D.T →
      CFSG.Quasithin.rk ↥(barSub V₀ V hV.isElemAbelian (conjSubgroup V g)) + mSub V₀ <
        mBar D.M V₀ V hV.isElemAbelian) :
    False := by
  have hN : ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    twelve_ten_one_zero D hx h61 h66 h127 h1114 h183 hV h0
      ((hV.mBarGT_iff_lt_mBar 2).2 hm2)
  obtain ⟨g, hgM, hAgT, hAgne⟩ :=
    s17_exists_conj_not_le_cTilde_of_add_lt D hx h61 h127 h1114 h162 hV h0 hm2
      (fun g hg hT => lt_of_le_of_lt (Nat.le_add_left _ _) (hrk g hg hT)) hN
  exact s17_false_of_conj_rk_add_lt D hx h61 h127 h1114 h162 h161 hV h0 hm2 hgM hAgT hAgne
    (hrk g hgM hAgT)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
