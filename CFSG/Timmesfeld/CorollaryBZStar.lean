module

public import CFSG.Timmesfeld.CorollaryBBasic
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.Timmesfeld.CorB

open Subgroup

theorem zStar_case {X : Type} [Group X] [Finite X] {t : X} (ht : orderOf t = 2)
    (hiso : ∀ τ : X, τ * t = t * τ → IsConj t τ → τ = t) :
    ∃ K : Subgroup X, K ≤ normalClosure ({t} : Set X) ∧
      (K.subgroupOf (normalClosure ({t} : Set X))).Normal ∧ Odd (Nat.card K) ∧
      normalClosure ({t} : Set X) = K ⊔ zpowers t := by
  have : Fintype X := Fintype.ofFinite X
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by decide)
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar X t ht1 ht2
    fun g hg => hiso _ hg (isConj_iff.mpr ⟨g, rfl⟩)
  have hU : (normalClosure ({t} : Set X)).Normal := normalClosure_normal
  have htU : t ∈ normalClosure ({t} : Set X) := cls_subset t (mem_cls_self t)
  refine ⟨N ⊓ normalClosure ({t} : Set X), inf_le_right, ?_, ?_, ?_⟩
  · exact (normal_inf_normal N _).subgroupOf _
  · exact Odd.of_dvd_nat hNodd (card_dvd_of_le inf_le_left)
  · refine le_antisymm ?_ (sup_le inf_le_right (zpowers_le.mpr htU))
    conv_lhs => rw [normalClosure_eq t]
    rw [closure_le]
    intro x hx
    obtain ⟨g, rfl⟩ := exists_conj_of_mem_cls hx
    have h1 : g * t * g⁻¹ * t⁻¹ ∈ N ⊓ normalClosure ({t} : Set X) :=
      mem_inf.mpr ⟨hN g, mul_mem (cls_subset t hx) (inv_mem htU)⟩
    rw [show g * t * g⁻¹ = g * t * g⁻¹ * t⁻¹ * t by group]
    exact mul_mem (mem_sup_left h1) (mem_sup_right (mem_zpowers t))

end CFSG.Timmesfeld.CorB
