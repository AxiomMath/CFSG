module

public import CFSG.LocalAnalysis.WeakClosure81.W16QDDih
public import CFSG.LocalAnalysis.WeakClosure81.W16QDFive
public import CFSG.LocalAnalysis.WeakClosure81.W16QTIMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

section Certified


theorem w16SixteenDich_holds (h1 : W16One G) (h5 : W16Five G) (h15 : W16Fifteen G)
    (h6 : W16SixI G) (hAut : AutRank166Input) (hK : KGroup1616Input)
    (hB : Borel166Input) : W16SixteenDich G := by
  intro hS M V₀ V U S H hcex hmin hV
  obtain ⟨X, _, φ, hbar, hshape, ho2⟩ := h6 hS hcex hmin hV
  have d : DichCfg M V₀ V U S H φ := ⟨⟨hS, h1, h5, h15, hcex, hmin, hV⟩, hbar, hshape, ho2⟩
  haveI : Finite X := Finite.of_surjective φ hbar.surjective
  have hYcard : Nat.card (SevenK.barSub (conjClosure V H) φ V) =
      2 ^ E3.mQuot V (iSub16 V H) := hshape.1
  have hYel := d.isElemAbelian_barSub
  have hgen := d.normalClosure_eq_top
  have hV₀card : Nat.card V₀ = 2 ^ mSub V₀ :=
    card_eq_two_pow_mSub (hcex.hyp.isPGroup.to_le hcex.hyp.h6.le)
  have hle : E3.mQuot V (iSub16 V H) ≤ mSub V₀ := d.cfg.mQuot_le_mSub
  have hQT : qSub16 V₀ V S H ≤ tSub16 V₀ S := by
    rcases hshape.2 with ⟨hn1, hPSL | hSz | hU3⟩ | ⟨hn1, hX, p, hp, -⟩
    · refine d.qSub16_le_tSub16_of_le (d.inf_le_sup_of_card_le ?_)
      rw [hYcard]
      exact card_le_of_isPGroup_psl (by omega) hPSL
    · exact d.qSub16_le_tSub16_of_borel hB hn1 (Or.inl hSz)
    · exact d.qSub16_le_tSub16_of_borel hB hn1 (Or.inr hU3)
    · have hY2 : Nat.card (SevenK.barSub (conjClosure V H) φ V) = 2 := by
        rw [hYcard, hn1]
        rfl
      refine d.qSub16_le_tSub16_of_le (d.inf_le_sup_of_card_le fun P hP => ?_)
      rw [hY2]
      exact card_le_of_isPGroup_oddCore hY2 hX P hP
  by_cases hoff : ∀ A ∈ elemFamilyIn 2 (tSub16 V₀ S), A ≤ qSub16 V₀ V S H
  · exact Or.inl ⟨hQT, hoff⟩
  right
  obtain ⟨A, hA, hAQ⟩ : ∃ A ∈ elemFamilyIn 2 (tSub16 V₀ S), ¬ A ≤ qSub16 V₀ V S H := by
    by_contra hc
    exact hoff fun A hA => by_contra fun h => hc ⟨A, hA, h⟩
  rcases hshape.2 with ⟨hn1, hPSL | hSz | hU3⟩ | ⟨hn1, hX, p, hp, hcyc | ⟨hext, hcard⟩⟩
  · have hNN := hAut.2.2.2 X _ _ hn1 hYcard hYel (Or.inl hPSL)
    obtain ⟨E, hE, hEc, hVE⟩ := d.exists_aut_subgroup hQT hNN hA hAQ
    have hEb := hAut.1 X _ _ hn1 hYcard hYel (Or.inl hPSL) E hE hEc
    have hm : mSub V₀ ≤ E3.mQuot V (iSub16 V H) := by
      have : 2 ^ mSub V₀ ≤ 2 ^ E3.mQuot V (iSub16 V H) := hV₀card ▸ hVE.trans hEb
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    exact ⟨d.exists_psl hPSL, le_antisymm hm hle⟩
  · have hNN := hAut.2.2.2 X _ _ hn1 hYcard hYel (Or.inr (Or.inl hSz))
    obtain ⟨E, hE, hEc, hVE⟩ := d.exists_aut_subgroup hQT hNN hA hAQ
    have hEb := hAut.1 X _ _ hn1 hYcard hYel (Or.inr hSz) E hE hEc
    have h2n := tiModule166_holds hK G h1 h5 h15 hS hcex hmin hV φ hbar hshape ho2 hn1 (Or.inl hSz)
    have : 2 ^ (2 * E3.mQuot V (iSub16 V H)) ≤ 2 ^ E3.mQuot V (iSub16 V H) :=
      (Nat.pow_le_pow_right (by norm_num) h2n).trans (hV₀card ▸ hVE.trans hEb)
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    omega
  · have hNN := hAut.2.2.2 X _ _ hn1 hYcard hYel (Or.inr (Or.inr hU3))
    obtain ⟨E, hE, hEc, hVE⟩ := d.exists_aut_subgroup hQT hNN hA hAQ
    have hEb := hAut.2.1 X _ _ hn1 hYcard hYel hU3 E hE hEc
    have h2n := tiModule166_holds hK G h1 h5 h15 hS hcex hmin hV φ hbar hshape ho2 hn1 (Or.inr hU3)
    have : 2 ^ (2 * E3.mQuot V (iSub16 V H)) ≤ 2 ^ (E3.mQuot V (iSub16 V H) + 1) :=
      (Nat.pow_le_pow_right (by norm_num) h2n).trans (hV₀card ▸ hVE.trans hEb)
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    omega
  · have hY2 : Nat.card (SevenK.barSub (conjClosure V H) φ V) = 2 := by
      rw [hYcard, hn1]
      rfl
    have hNN := fun α hα hN => eq_one_of_forall_normalizes_of_card_two hY2 hgen α hα hN
    obtain ⟨E, hE, hEc, hVE⟩ := d.exists_aut_subgroup hQT hNN hA hAQ
    have hEb := hAut.2.2.1 X _ hY2 hYel hX ⟨p, hp, hcyc⟩ E hE hEc
    have hm : mSub V₀ ≤ 1 := by
      have : 2 ^ mSub V₀ ≤ 2 ^ 1 := hV₀card ▸ hVE.trans hEb
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    have hm1 : mSub V₀ = 1 := le_antisymm hm (hn1 ▸ hle)
    exact ⟨d.exists_psl_of_dihedral hn1 hX ⟨p, hp, hcyc⟩ hm1, hm1.trans hn1.symm⟩
  · have hY2 : Nat.card (SevenK.barSub (conjClosure V H) φ V) = 2 := by
      rw [hYcard, hn1]
      rfl
    exact absurd (d.le_qSub16_of_heis hQT ⟨hY2, hX, hp, hext, hcard, hgen⟩ A hA) hAQ

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
