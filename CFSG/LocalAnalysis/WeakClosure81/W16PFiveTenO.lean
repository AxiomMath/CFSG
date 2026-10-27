module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveTenJ
public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveNine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem IsMinFam16.inCalO_conj_of_not_le (h1 : W16One G) (h5 : W16Five G) (hS : Std15 G)
    (h : Cex16 M V₀ V U S) (hH : IsMinFam16 M U S H) (hV : ¬ V ≤ pCoreOf 2 H)
    (hQ : pCoreOf 2 (conjClosure V H) ≤ centralizer (iSub16 V H : Set G)) {x : G}
    (hxS : conjSubgroup V x ≤ S)
    (h9 : ∀ a ∈ conjSubgroup V x, ∃ v ∈ V, ∀ k ∈ conjClosure V H,
      (a * v⁻¹) * k * (a * v⁻¹)⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure V H))
    {k : G} (hk : k ∈ conjClosure V H) (hk1 : ¬ conjSubgroup V k ≤ conjSubgroup M x)
    (hk2 : ¬ conjSubgroup V x ≤ conjSubgroup M k) :
    InCalO (E3.mQuot V (U ⊔ V₀)) (conjSubgroup M x) (conjSubgroup V₀ x) (conjSubgroup V x)
      (x⁻¹ * k) := by
  have hF : Fam16 M U S H := hH.1
  have hKH : conjClosure V H ≤ H :=
    conjClosure_le fun m hm z hz =>
      H.mul_mem (H.mul_mem hm ((h.V_le_S.trans hF.1) hz)) (H.inv_mem hm)
  have hkH : k ∈ H := hKH hk
  have hInorm : H ≤ Subgroup.normalizer (iSub16 V H : Set G) :=
    le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hIk : conjSubgroup (iSub16 V H) k = iSub16 V H :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hInorm hkH)
  have hV0p : V₀ ≤ pCoreOf 2 H := h.V₀_le_pCoreOf h5 hS hF hV
  have hV0I : V₀ ≤ iSub16 V H := (le_inf h.hyp.h6.le hV0p).trans (le_conjClosure _ _)
  have hV0k_le_I : conjSubgroup V₀ k ≤ iSub16 V H := by
    rw [← hIk]
    exact E3.conjSubgroup_mono_left k hV0I
  have hCI_Mk : centralizer (iSub16 V H : Set G) ≤ conjSubgroup M k := by
    have hnorm : Subgroup.normalizer (conjSubgroup V₀ k : Set G) = conjSubgroup M k := by
      rw [← E3.conjSubgroup_normalizer V₀ k, h.hyp.normalizer₀]
    exact (Subgroup.centralizer_le hV0k_le_I).trans
      ((Subgroup.centralizer_le_normalizer _).trans hnorm.le)
  have hmD : E3.mQuot (conjSubgroup V x)
      (conjSubgroup V x ⊓ centralizer (iSub16 V H : Set G)) ≤ E3.mQuot V (U ⊔ V₀) :=
    IsMinFam16.mQuot_inf_centralizer_le h1 h5 hS h hH hV hQ hxS h9
  have hI_le_Mx : iSub16 V H ≤ conjSubgroup M x :=
    (Subgroup.le_centralizer_iff.mpr (inf_le_right :
      conjSubgroup V x ⊓ centralizer (iSub16 V H : Set G) ≤
        centralizer (iSub16 V H : Set G))).trans
      (h.centralizer_le_conj_of_mQuot_le inf_le_left hmD)
  have hii : E3.mQuot (conjSubgroup V x) (conjSubgroup M k) ≤ E3.mQuot V (U ⊔ V₀) :=
    (E3.mQuot_mono (inf_le_right.trans hCI_Mk)).trans hmD
  have hVI_eq : conjSubgroup V k ⊓ iSub16 V H = conjSubgroup (U ⊔ V₀) k := by
    rw [← hIk, ← E3.conjSubgroup_inf, h.inf_iSub16_eq h1 h5 hS hF hV]
  have hv : E3.mQuot (conjSubgroup V k) (conjSubgroup M x) ≤ E3.mQuot V (U ⊔ V₀) := by
    calc E3.mQuot (conjSubgroup V k) (conjSubgroup M x)
        ≤ E3.mQuot (conjSubgroup V k) (conjSubgroup V k ⊓ iSub16 V H) :=
          E3.mQuot_mono (inf_le_right.trans hI_le_Mx)
      _ = E3.mQuot (conjSubgroup V k) (conjSubgroup (U ⊔ V₀) k) := by rw [hVI_eq]
      _ = E3.mQuot V (U ⊔ V₀) := E3.mQuot_conjSubgroup V (U ⊔ V₀) k
  have hiii : conjSubgroup V₀ x ≠ ⊥ → conjSubgroup V₀ x ⊓ conjSubgroup M k ≠ ⊥ := by
    intro _
    have h0 := Cex16.conj_inf_centralizer_ne_bot h1 hS h hF hxS hI_le_Mx
    exact fun hbot =>
      h0 (le_bot_iff.mp ((le_inf inf_le_left (inf_le_right.trans hCI_Mk)).trans hbot.le))
  have hV0k_le_Mx : conjSubgroup V₀ k ≤ conjSubgroup M x := hV0k_le_I.trans hI_le_Mx
  have hvi : conjSubgroup V₀ x ≠ ⊥ → conjSubgroup V₀ k ⊓ conjSubgroup M x ≠ ⊥ := by
    intro _
    have hV0k_ne : conjSubgroup V₀ k ≠ ⊥ :=
      fun hk0 => h.hyp.ne_bot (conjSubgroup_eq_bot_iff.mp hk0)
    rwa [inf_eq_left.mpr hV0k_le_Mx]
  unfold InCalO OFirst ODual
  simp only [conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  exact ⟨⟨hk1, hii, hiii⟩, hk2, hv, hvi⟩

end CFSG.LocalAnalysis.WeakClosure81

end
