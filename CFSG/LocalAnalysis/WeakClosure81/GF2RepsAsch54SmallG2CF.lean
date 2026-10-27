module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SmallCF

import CFSG.GH74.Generic.BProg.B2.GenLocG2OuterShape
import CFSG.GH74.SectionalRankExtension

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch80G2

open Subgroup CFSG.Quasithin
open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab (Shape mem_sup_of_commute)
open CFSG.GH74.Generic.BProg.B2.GenLocG2OuterShape (mem_E_or two_ne_zero₁ two_ne_zero₂)

theorem shape_quotient_comm {K : Type} [Group K] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    (S : Shape K F₁ F₂) [(S.I₁ ⊔ S.I₂).Normal] (x y : K ⧸ (S.I₁ ⊔ S.I₂)) : x * y = y * x := by
  have hval : ∀ w : K ⧸ (S.I₁ ⊔ S.I₂), w = 1 ∨ w = ((S.t : K) : K ⧸ (S.I₁ ⊔ S.I₂)) := by
    intro w
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective w
    rcases mem_E_or S k with h | h
    · exact Or.inl ((QuotientGroup.eq_one_iff k).2 h)
    · right
      have h1 : ((k * S.t : K) : K ⧸ (S.I₁ ⊔ S.I₂)) = 1 := (QuotientGroup.eq_one_iff _).2 h
      have h2 : ((S.t * S.t : K) : K ⧸ (S.I₁ ⊔ S.I₂)) = 1 := by
        rw [S.t_sq, QuotientGroup.mk_one]
      rw [QuotientGroup.mk_mul] at h1 h2
      exact mul_right_cancel (h1.trans h2.symm)
  rcases hval x with rfl | rfl <;> rcases hval y with rfl | rfl <;> simp

theorem shape_not_isCompositionFactor {P : ∀ (X : Type) [Group X], Prop}
    (hP : ∀ (L : Type) [Group L] [Finite L], P L →
      (∃ a b : L, a * b ≠ b * a) ∧ ¬ CFSG.GH74.SectionalTwoRankLE L 2)
    {K : Type} [Group K] [Finite K] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
    [Finite F₂] (S : Shape K F₁ F₂) (L : Type) [Group L] (h : E1.IsCompositionFactor K L) :
    ¬ P L := by
  have := S.normal₁
  have := S.normal₂
  have hJn : (S.I₁ ⊔ S.I₂).Normal := Subgroup.sup_normal S.I₁ S.I₂
  have hP2 : ∀ (L : Type) [Group L] [Finite L], P L → ¬ CFSG.GH74.SectionalTwoRankLE L 2 :=
    fun L _ _ hL => (hP L hL).2
  refine not_isCompositionFactor_of_normal (S.I₁ ⊔ S.I₂) ?_ ?_ L h
  · have : (S.I₁.subgroupOf (S.I₁ ⊔ S.I₂)).Normal := Subgroup.normal_subgroupOf
    refine not_isCompositionFactor_of_normal (S.I₁.subgroupOf (S.I₁ ⊔ S.I₂)) ?_ ?_
    · refine not_isCompositionFactor_of_sectionalTwoRankLE hP2 ?_
      exact CFSG.GH74.SectionalTwoRankLE.of_mulEquiv
        ((Subgroup.subgroupOfEquivOfLe le_sup_left).trans S.e₁).symm
        (CFSG.GH74.SectionalTwoRankLE.specialLinearGroup F₁ (two_ne_zero₁ S))
    · refine not_isCompositionFactor_of_sectionalTwoRankLE hP2 ?_
      let f : ↥S.I₂ →* ↥(S.I₁ ⊔ S.I₂) ⧸ S.I₁.subgroupOf (S.I₁ ⊔ S.I₂) :=
        (QuotientGroup.mk' _).comp (Subgroup.inclusion le_sup_right)
      have hf : Function.Surjective f := by
        intro w
        obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective w
        obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute S.comm hx
        refine ⟨⟨b, hb⟩, ?_⟩
        show ((⟨b, _⟩ : ↥(S.I₁ ⊔ S.I₂)) : ↥(S.I₁ ⊔ S.I₂) ⧸ S.I₁.subgroupOf (S.I₁ ⊔ S.I₂)) =
          ((⟨a * b, hx⟩ : ↥(S.I₁ ⊔ S.I₂)) : ↥(S.I₁ ⊔ S.I₂) ⧸ S.I₁.subgroupOf (S.I₁ ⊔ S.I₂))
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        show b⁻¹ * (a * b) ∈ S.I₁
        have e : b⁻¹ * (a * b) = a := by rw [S.comm a ha b hb]; group
        rw [e]
        exact ha
      exact CFSG.GH74.SectionalTwoRankLE.of_surjective f hf
        (CFSG.GH74.SectionalTwoRankLE.of_mulEquiv S.e₂.symm
          (CFSG.GH74.SectionalTwoRankLE.specialLinearGroup F₂ (two_ne_zero₂ S)))
  · exact not_isCompositionFactor_of_isSolvable (fun L _ _ hL => (hP L hL).1)
      (isSolvable_of_comm (shape_quotient_comm S))

end CFSG.LocalAnalysis.WeakClosure81.Asch80G2

end
