module

public import CFSG.LocalAnalysis.WeakClosure81.W16Setup
public import CFSG.LocalAnalysis.WeakClosure81.SixFiveH

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S : Subgroup G}

section Certified


theorem IsMinFam16.exists_conj_eq_of_inCalO (h : Cex16 M V₀ V U S) {x k : G}
    (hO : InCalO (E3.mQuot V (U ⊔ V₀)) (conjSubgroup M x) (conjSubgroup V₀ x)
      (conjSubgroup V x) (x⁻¹ * k)) :
    ∃ l ∈ conjSubgroup V x ⊔ conjSubgroup V k,
      conjSubgroup V k = conjSubgroup (conjSubgroup V x) l := by
  have hH := h.hyp.h6
  have hM : M ≤ normalizer (V : Set G) := le_of_eq hH.normalizer_eq.symm
  have hM₀ : M ≤ normalizer (V₀ : Set G) := hH.le_normalizer₀
  have hVx : IsElemAbelian 2 (conjSubgroup V x) :=
    E3.isElemAbelian_conjSubgroup hH.elemAbelian x
  have hV₀x : conjSubgroup V₀ x ≤ conjSubgroup V x := E3.conjSubgroup_mono_left x hH.le
  have hMx : conjSubgroup M x ≤ normalizer (conjSubgroup V x : Set G) := by
    refine (E3.conjSubgroup_mono_left x hM).trans ?_
    rw [E3.conjSubgroup_normalizer]
  have hM₀x : conjSubgroup M x ≤ normalizer (conjSubgroup V₀ x : Set G) := by
    refine (E3.conjSubgroup_mono_left x hM₀).trans ?_
    rw [E3.conjSubgroup_normalizer]
  have hn : E3.mQuot V (U ⊔ V₀) <
      mBar (conjSubgroup M x) (conjSubgroup V₀ x) (conjSubgroup V x) hVx := by
    rw [mBar_conj M V₀ V hH.elemAbelian hH.le hM hM₀ x]
    exact h.n_lt_mBar
  have h65 : Hyp65 (E3.mQuot V (U ⊔ V₀)) (conjSubgroup M x) (conjSubgroup V₀ x)
      (conjSubgroup V x) (x⁻¹ * k) :=
    ⟨hVx, hV₀x, fun hbot => h.hyp.ne_bot (conjSubgroup_eq_bot_iff.1 hbot),
      by rw [← E3.conjSubgroup_normalizer, hH.normalizer_eq],
      by rw [← E3.conjSubgroup_normalizer, h.hyp.normalizer₀],
      isTI_conj h.hyp.isTI x,
      (six_six hVx hV₀x hMx hM₀x hn (x⁻¹ * k)).1 hO⟩
  obtain ⟨l, hl, hconj⟩ := Hyp65.exists_conj h65
  have hL : LOf (conjSubgroup V x) (x⁻¹ * k) = conjSubgroup V x ⊔ conjSubgroup V k := by
    rw [LOf, conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  have hconj_eq : conjSubgroup (conjSubgroup V x) (x⁻¹ * k) = conjSubgroup V k := by
    rw [conjSubgroup_conjSubgroup, mul_inv_cancel_left]
  refine ⟨l, ?_, ?_⟩
  · rwa [hL] at hl
  · rw [← hconj_eq]
    exact hconj

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
