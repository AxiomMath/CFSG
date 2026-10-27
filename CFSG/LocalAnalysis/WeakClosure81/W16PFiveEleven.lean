module

public import CFSG.LocalAnalysis.WeakClosure81.W16PFiveEight

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {M V₀ V U S H : Subgroup G} {g : G} {X T : Subgroup G}

theorem Hyp167.inf_centralizer_le_of_inf_eq_bot (h1 : W16One G) (hS : Std15 G)
    (hV₀ : V₀ ≤ pCoreOf 2 H) (hX : Hyp167 M V₀ V U S H g X T)
    (hBE : conjSubgroup V₀ g ⊓ eSub V₀ X T = ⊥) {D : Subgroup G} (hD : D ≤ conjSubgroup V g)
    (hm : E3.mQuot (conjSubgroup V g) D <
      Min.min (E3.mQuot V (U ⊔ V₀) + mSub V₀) (mBar M V₀ V hX.cex.hyp.h6.elemAbelian)) :
    eSub V₀ X T ⊓ centralizer (D : Set G) ≤ centralizer (conjSubgroup V g : Set G) := by
  have hV := hX.cex.hyp.h6.elemAbelian
  have hVg := E3.isElemAbelian_conjSubgroup hV g
  have hV₀g : conjSubgroup V₀ g ≤ conjSubgroup V g :=
    E3.conjSubgroup_mono_left g hX.cex.hyp.h6.le
  have hMnormg : normalizer (conjSubgroup V g : Set G) = conjSubgroup M g := by
    rw [← E3.conjSubgroup_normalizer, hX.cex.hyp.h6.normalizer_eq]
  have hM₀g : conjSubgroup M g ≤ normalizer (conjSubgroup V₀ g : Set G) := by
    refine (E3.conjSubgroup_mono_left g hX.cex.hyp.h6.le_normalizer₀).trans ?_
    rw [E3.conjSubgroup_normalizer]
  have hE : IsElemAbelian 2 (eSub V₀ X T) := Hyp167.isElemAbelian_eSub h1 hS hV₀ hX
  have hXT : conjSubgroup V g ≤ X := hX.A_le_T.trans (hX.sylow.le.trans inf_le_left)
  have hAE : conjSubgroup V g ≤ Subgroup.normalizer (eSub V₀ X T : Set G) :=
    hXT.trans (le_normalizer_conjClosure (V₀ ⊓ Subgroup.centralizer (T : Set G)) X)
  have hq₁ : (E3.mQuot (conjSubgroup V g) D : ℕ∞) <
      ((E3.mQuot V (U ⊔ V₀) + mSub V₀ : ℕ) : ℕ∞) := by
    exact_mod_cast lt_of_lt_of_le hm (min_le_left _ _)
  have hq₂ : (E3.mQuot (conjSubgroup V g) D : ℕ∞) <
      ((mBar M V₀ V hV : ℕ) : ℕ∞) := by
    exact_mod_cast lt_of_lt_of_le hm (min_le_right _ _)
  have hlt : (E3.mQuot (conjSubgroup V g) D : ℕ∞) + ((0 : ℕ) : ℕ∞) <
      Min.min (rMV (conjSubgroup M g) (conjSubgroup V g))
        (mBar (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) hVg : ℕ∞) := by
    rw [Nat.cast_zero, add_zero,
      rMV_conj hX.cex.hyp.h6.normalizer_eq g,
      mBar_conj M V₀ V hV hX.cex.hyp.h6.le
        (hX.cex.hyp.h6.normalizer_eq ▸ le_rfl) hX.cex.hyp.h6.le_normalizer₀ g,
      hX.cex.rMV_eq]
    exact lt_min hq₁ hq₂
  have h14 := commutator_le_inf_of_mQuot_add_lt (M := conjSubgroup M g)
    (V₀ := conjSubgroup V₀ g) (V := conjSubgroup V g) (A := conjSubgroup V g)
    (B := D) (E := eSub V₀ X T) hVg hV₀g hMnormg.ge hM₀g le_rfl (i := 0)
    (E3.mQuot_self _) hD hAE hE.isPGroup hlt
  have hbot : eSub V₀ X T ⊓ conjSubgroup V₀ g = ⊥ := by
    rw [inf_comm]
    exact hBE
  have hcomm : ⁅eSub V₀ X T ⊓ centralizer (D : Set G), conjSubgroup V g⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact h14.trans (le_of_eq hbot)
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

end CFSG.LocalAnalysis.WeakClosure81

end
