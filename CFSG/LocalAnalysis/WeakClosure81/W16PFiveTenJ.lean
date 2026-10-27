module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveIa

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G}

theorem Cex16.centralizer_le_conj_of_mQuot_le (h : Cex16 M V₀ V U S) {x : G} {D : Subgroup G}
    (hD : D ≤ conjSubgroup V x)
    (hm : E3.mQuot (conjSubgroup V x) D ≤ E3.mQuot V (U ⊔ V₀)) :
    centralizer (D : Set G) ≤ conjSubgroup M x := by
  refine centralizer_le_of_mQuot_lt_rMV (M := conjSubgroup M x) (V := conjSubgroup V x)
    (X := D) hD ?_
  rw [rMV_conj h.hyp.h6.normalizer_eq x, h.rMV_eq]
  have h1 : ((E3.mQuot (conjSubgroup V x) D : ℕ) : ℕ∞) ≤
      ((E3.mQuot V (U ⊔ V₀) : ℕ) : ℕ∞) := by
    exact_mod_cast hm
  have h2 : ((E3.mQuot V (U ⊔ V₀) : ℕ) : ℕ∞) <
      ((E3.mQuot V (U ⊔ V₀) + mSub V₀ : ℕ) : ℕ∞) := by
    have hV0 : 1 ≤ mSub V₀ := by
      by_contra hlt
      have h0 : mSub V₀ = 0 := by omega
      have hcard : Nat.card V₀ = 1 := by
        rw [card_eq_two_pow_mSub (CFSG.Open.IsElemAbelian.isPGroup h.hyp.elemAbelian₀), h0]
        rfl
      exact h.hyp.ne_bot ((Subgroup.eq_bot_iff_card V₀).2 hcard)
    exact_mod_cast (show E3.mQuot V (U ⊔ V₀) < E3.mQuot V (U ⊔ V₀) + mSub V₀ by omega)
  exact lt_of_le_of_lt h1 h2

theorem Cex16.conj_inf_centralizer_ne_bot (h1 : W16One G) (hS : Std15 G) (h : Cex16 M V₀ V U S)
    (hF : Fam16 M U S H) {x : G} (hxS : conjSubgroup V x ≤ S)
    (hI : iSub16 V H ≤ conjSubgroup M x) :
    conjSubgroup V₀ x ⊓ centralizer (iSub16 V H : Set G) ≠ ⊥ := by
  set B : Subgroup G := conjSubgroup V₀ x with hB
  set I : Subgroup G := iSub16 V H with hIdef
  change B ⊓ centralizer (I : Set G) ≠ ⊥
  have hB_le_Vx : B ≤ conjSubgroup V x := by
    rw [hB]
    exact E3.conjSubgroup_mono_left x h.hyp.h6.le
  have hB_le_H : B ≤ H := hB_le_Vx.trans (hxS.trans hF.1)
  have hIab : IsElemAbelian 2 I := by
    rw [hIdef]
    exact h.isElemAbelian_iSub16 h1 hS hF
  have hI_le_cI : I ≤ centralizer (I : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hIab.1
  have hH_le_NI : H ≤ Subgroup.normalizer (I : Set G) := by
    rw [hIdef, iSub16]
    exact le_normalizer_conjClosure (V ⊓ pCoreOf 2 H) H
  have hB_le_NI : B ≤ Subgroup.normalizer (I : Set G) := hB_le_H.trans hH_le_NI
  have hI_le_NB : I ≤ Subgroup.normalizer (B : Set G) := by
    have hMx : conjSubgroup M x = Subgroup.normalizer (conjSubgroup V₀ x : Set G) := by
      rw [← h.hyp.normalizer₀]
      exact E3.conjSubgroup_normalizer V₀ x
    rw [hB]
    exact (hIdef.symm ▸ hI).trans (le_of_eq hMx)
  have hcomm_le_B : ⁅B, I⁆ ≤ B :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hI_le_NB
  have hcomm_le_I : ⁅B, I⁆ ≤ I :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hB_le_NI
  have hcomm_le : ⁅B, I⁆ ≤ B ⊓ centralizer (I : Set G) :=
    le_inf hcomm_le_B (hcomm_le_I.trans hI_le_cI)
  have hB_ne_bot : B ≠ ⊥ := by
    rw [hB]
    intro hb
    exact h.hyp.ne_bot (conjSubgroup_eq_bot_iff.mp hb)
  intro hbot
  have hcomm_bot : ⁅B, I⁆ = ⊥ :=
    le_bot_iff.mp (hcomm_le.trans (le_of_eq hbot))
  have hB_le_cI : B ≤ centralizer (I : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_bot
  exact hB_ne_bot (le_bot_iff.mp ((le_inf le_rfl hB_le_cI).trans (le_of_eq hbot)))

end CFSG.LocalAnalysis.WeakClosure81

end
