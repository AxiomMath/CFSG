module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4ModelX
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenStruct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16c4_lemX
    (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (F : UFrame V₀ V hV L) {g : G} (h : Hyp64 1 D.M V₀ V g) : False := by
  have hgen : GenHyp D.M V g := genHyp_of_hyp64 h
  have hBM : BOf D.M V g ≤ D.M := inf_le_right
  have hBV : BOf D.M V g ≤ conjSubgroup V g := inf_le_left
  have hNV : NOf D.M V g ≤ V := inf_le_left.trans inf_le_left
  have hBel : IsElemAbelian 2 (BOf D.M V g) :=
    B2F.isElemAbelian_mono hBV (E3.isElemAbelian_conjSubgroup hV g)
  have hE2 : IsElemAbelian2 (barSub V₀ V hV (BOf D.M V g)) := isElemAbelian2_barSub hV hBel
  have hEN : barSub V₀ V hV (BOf D.M V g) ≤
      normalizer (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
    (barSub_mono V₀ V hV hBM).trans (F.Mbar_le_normalizer hS)
  have hE1 : barSub V₀ V hV (BOf D.M V g) ≠ ⊥ := barSub_BOf_ne_bot h hgen
  have hfix : fixV (barSub V₀ V hV (BOf D.M V g)) = imgTil V₀ V hV (NOf D.M V g) := by
    have h1 := imgTil_preTil V₀ V hV (fixV (barSub V₀ V hV (BOf D.M V g)))
    rw [preTil_fixV_barSub_BOf h hgen, imgTil_sup_V₀ hV hNV h.le] at h1
    exact h1.symm
  have hidx : (imgTil V₀ V hV (UOf D.M V g)).index = 2 :=
    index_imgTil_UOf_eq_two h hgen (mQuot_UOf_le h)
  have hUt : Nat.card (imgTil V₀ V hV (UOf D.M V g)) * 2 = Nat.card (Vtil V₀ V hV) := by
    rw [← hidx]
    exact Subgroup.card_mul_index _
  have hmul := card_barSub_mul_index_eq h hgen
  rw [hidx] at hmul
  have hcard : Nat.card (barSub V₀ V hV (BOf D.M V g)) * 2 *
      Nat.card (fixV (barSub V₀ V hV (BOf D.M V g))) = Nat.card (Vtil V₀ V hV) := by
    have h2 := Subgroup.card_mul_index (imgTil V₀ V hV (NOf D.M V g))
    rw [hfix, ← h2, ← hmul]
    ring
  have hUb : ∀ b ∈ barSub V₀ V hV (BOf D.M V g), b ≠ 1 → ∀ w : Vtil V₀ V hV,
      w ∈ imgTil V₀ V hV (UOf D.M V g) ↔ b w * w⁻¹ ∈ fixV (barSub V₀ V hV (BOf D.M V g)) := by
    intro b hb hb1 w
    rw [hfix]
    exact ⟨fun hw => apply_mul_inv_mem_imgTil_NOf h hgen hb hb1 hw,
      fun hw => mem_imgTil_UOf_of_apply_mul_inv_mem h hgen hb hb1 hw⟩
  exact F.s16c4_modelX hEN hE2 hE1 hUt hUb hcard

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
