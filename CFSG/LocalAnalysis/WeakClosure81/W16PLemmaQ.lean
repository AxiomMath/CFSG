module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CfgLemmaQ

variable {M V₀ V C : Subgroup G} {h : G}

section Certified


theorem le_sup_inf_centralizer (q : CfgLemmaQ M V₀ V h C) :
    V ≤ V₀ ⊔ (V ⊓ centralizer ((V₀ ⊔ conjSubgroup V₀ h : Subgroup G) : Set G)) := by
  refine q.le_sup.trans (sup_le ?_ le_sup_left)
  intro c hc
  obtain ⟨a, ha, hτY, hτX⟩ := q.exists_mul_commutator_mem hc
  have hτ : a * c ∈ V := V.mul_mem (q.hyp.h6.le ha) (q.le hc)
  obtain ⟨y, hy, hyC⟩ := q.exists_mem_mul_inv_mem_centralizer hτ hτY hτX
  have hmem : a * c * y⁻¹ ∈
      V ⊓ centralizer ((V₀ ⊔ conjSubgroup V₀ h : Subgroup G) : Set G) :=
    ⟨V.mul_mem hτ (V.inv_mem (q.hyp.h6.le hy)), hyC⟩
  have e : c = a⁻¹ * (a * c * y⁻¹) * y := by group
  rw [e]
  exact mul_mem (mul_mem (mem_sup_left (inv_mem ha)) (mem_sup_right hmem)) (mem_sup_left hy)

theorem false (h152 : Thm152 G) (q : CfgLemmaQ M V₀ V h C)
    (hm : 1 < mBar M V₀ V q.hyp.h6.elemAbelian) : False :=
  q.false_of_le h152 hm q.le_sup_inf_centralizer

end Certified

end CfgLemmaQ

end CFSG.LocalAnalysis.WeakClosure81

end
