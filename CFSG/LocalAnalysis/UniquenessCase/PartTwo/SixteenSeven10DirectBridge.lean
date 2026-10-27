module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38A
public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenStruct

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s16c1610_directData_of_calOStar (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    {g : G} (hO : InCalOStar D.k D.M V₀ V g) :
    ∃ (Ut : Subgroup (Vtil V₀ V h.isElemAbelian))
      (B : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))),
      B ≤ Mbar D.M V₀ V h.isElemAbelian ∧ B ≠ ⊥ ∧ IsElemAbelian2 B ∧ Ut ≠ ⊤ ∧
        rkIdx Ut ≤ D.k ∧
        (∀ b ∈ B, b ≠ 1 → fixV (Subgroup.zpowers b) ≤ Ut) ∧
        (∀ b ∈ B, b ≠ 1 → ∀ w, w ∈ Ut ↔ w * (b w)⁻¹ ∈ fixV B) ∧
        rkIdx (fixV B) = rk ↥B + rkIdx Ut := by
  have h64 : Hyp64 D.k D.M V₀ V g := hyp64_of_hyp125 h hO
  have hgen : GenHyp D.M V g := genHyp_of_hyp64 h64
  have hV := h64.elemAbelian
  have hM : D.M ≤ normalizer (V : Set G) := h64.normalizer_eq.symm.le
  have hNV : NOf D.M V g ≤ V := inf_le_left.trans inf_le_left
  have hfix : fixV (barSub V₀ V hV (BOf D.M V g)) = imgTil V₀ V hV (NOf D.M V g) := by
    have h1 := imgTil_preTil V₀ V hV (fixV (barSub V₀ V hV (BOf D.M V g)))
    rw [preTil_fixV_barSub_BOf h64 hgen, imgTil_sup_V₀ hV hNV h64.le] at h1
    exact h1.symm
  refine ⟨imgTil V₀ V hV (UOf D.M V g), barSub V₀ V hV (BOf D.M V g),
    barSub_mono V₀ V hV inf_le_right, barSub_BOf_ne_bot_uncond h64,
    isElemAbelian2_barSub_BOf h64, imgTil_UOf_ne_top h64 hgen, rkIdx_imgTil_UOf_le h64 hgen,
    fun b hb hb1 => fixV_zpowers_le_imgTil_UOf h64 hgen hb hb1, ?_, ?_⟩
  · intro b hb hb1 w
    obtain ⟨⟨β, hβs⟩, hβB, rfl⟩ := (mem_barSub V₀ V hV (BOf D.M V g) b).1 hb
    have hβC : β ∉ F11.CTilde D.M V₀ V := fun hc => by
      obtain ⟨-, hs, h1⟩ := (mem_cTilde_iff hV hM).1 hc
      exact hb1 h1
    exact mem_imgTil_UOf_iff h64 hgen hβB hβC hβs w
  · have hcard := card_barSub_mul_index_eq h64 hgen
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hB0 : Nat.card (barSub V₀ V hV (BOf D.M V g)) ≠ 0 := Nat.card_pos.ne'
    have hU0 : (imgTil V₀ V hV (UOf D.M V g)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    unfold rk rkIdx
    rw [hfix, ← padicValNat.mul hB0 hU0, hcard]

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
