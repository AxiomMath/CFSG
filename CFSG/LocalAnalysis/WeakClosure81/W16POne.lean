module

public import CFSG.LocalAnalysis.WeakClosure81.W16Inputs
public import CFSG.LocalAnalysis.WeakClosure81.W16PIrr
public import CFSG.LocalAnalysis.WeakClosure81.W16POneFirst
public import CFSG.LocalAnalysis.WeakClosure81.W16POneSecond
public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQ

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Certified


namespace Cfg161

variable {M V₀ V U : Subgroup G} {g : G}

theorem dichotomy (hTim : TimmesfeldTIRootInput) (h152 : Thm152 G) (c : Cfg161 M V₀ V U g) :
    V₀ ≤ centralizer (conjSubgroup V g : Set G) ∨
      V ≤ V₀ ⊔ (V ⊓ centralizer (conjSubgroup V g : Set G)) := by
  have hVJ : V ≤ conjSubgroup M g := c.le_conjSubgroup h152
  have hE : IsElemAbelian 2 (conjSubgroup V g) :=
    E3.isElemAbelian_conjSubgroup c.hyp.h6.elemAbelian g
  have hJ : conjSubgroup M g ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    rw [← c.hyp.h6.normalizer_eq, conjSubgroup_normalizer]
  obtain ⟨D⟩ := exists_modDataE hE hJ
  have hA : D.img V ∈ D.conjImgFam V :=
    ⟨1, (conjSubgroup M g).one_mem, by rw [conjSubgroup_one]⟩
  rcases eq_bot_or_eq_of_assumption131 hTim (c.assumption131 h152 D) (c.mRank_le h152 D)
      (c.conjImgSpace_le_fixSub h152 D) hA (D.img_mono c.hyp.h6.le)
      (c.normalizer_img_le h152 D) with h0 | h0
  · exact Or.inl (D.le_centralizer_of_img_eq_bot (c.hyp.h6.le.trans hVJ) h0)
  · exact Or.inr (D.le_sup_of_img_eq c.hyp.h6.le hVJ h0)

end Cfg161

theorem w16One_of_inputs (hTim : TimmesfeldTIRootInput) (h152 : Thm152 G) : W16One G := by
  intro _ M V₀ V U hyp hm hUV hlt
  refine E3.wClos_le_of_forall fun A hA => ?_
  obtain ⟨hAX, g, hAg, hq⟩ := hA
  have hAeq : A = conjSubgroup V g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hyp.isPGroup g) hAg).1 hq
  subst hAeq
  by_contra hcon
  have hnc : ¬ ∀ x ∈ V, ∀ y ∈ conjSubgroup V g, x * y = y * x := by
    intro hall
    refine hcon fun y hy => Subgroup.mem_centralizer_iff.mpr fun x hx => hall x hx y hy
  have c : Cfg161 M V₀ V U g := ⟨hyp, hm, hUV, hlt, hAX, hnc⟩
  rcases c.dichotomy hTim h152 with h0 | h0
  · exact c.false_of_le_centralizer h152 h0
  · obtain ⟨h, -, q⟩ := c.exists_cfgLemmaQ h152 h0
    exact q.false h152 hm

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end
