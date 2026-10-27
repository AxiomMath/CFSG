module

public import CFSG.CharacterTheory.PSL2Table.Basic
import CFSG.LocalAnalysis.QuasithinUnique.K1.OddClassicalPSL2

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG.PSL2Table
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem exists_inv_comm_of_isConj_l2odd189 {S : Subgroup PSL(2, F)} [IsCyclic S] {w₀ : PSL(2, F)}
    (hw₀ : ∀ a ∈ S, w₀ * a * w₀⁻¹ = a⁻¹) (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    {x x₀ : PSL(2, F)} (hx₀ : x₀ ∈ S) (hc : IsConj x x₀) :
    ∃ w y : PSL(2, F), w * x * w⁻¹ = x⁻¹ ∧ y * x = x * y ∧ orderOf y = Nat.card S ∧
      orderOf x ∣ Nat.card S := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hx : x = c⁻¹ * x₀ * c := by rw [← hc]; group
  have hord : ∀ g : PSL(2, F), orderOf (c⁻¹ * g * c) = orderOf g := fun g => by
    have := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) g
    rwa [MulAut.conj_apply, inv_inv] at this
  refine ⟨c⁻¹ * w₀ * c, c⁻¹ * g₀ * c, ?_, ?_, ?_, ?_⟩
  · rw [hx]
    calc c⁻¹ * w₀ * c * (c⁻¹ * x₀ * c) * (c⁻¹ * w₀ * c)⁻¹ = c⁻¹ * (w₀ * x₀ * w₀⁻¹) * c := by
          group
      _ = (c⁻¹ * x₀ * c)⁻¹ := by rw [hw₀ x₀ hx₀]; group
  · rw [hx]
    calc c⁻¹ * g₀ * c * (c⁻¹ * x₀ * c) = c⁻¹ * (g₀ * x₀) * c := by group
      _ = c⁻¹ * (x₀ * g₀) * c := by rw [hcomm _ g₀.2 _ hx₀]
      _ = c⁻¹ * x₀ * c * (c⁻¹ * g₀ * c) := by group
  · rw [hord, Subgroup.orderOf_coe, hg₀]
  · rw [hx, hord]
    exact Subgroup.orderOf_dvd_natCard S hx₀

variable [Fintype F] [DecidableEq F]

theorem exists_inv_comm_l2odd189 (hF : ringChar F ≠ 2) (hq : 5 ≤ Fintype.card F)
    (h3 : ¬ 3 ∣ Fintype.card F) {x : PSL(2, F)} (hx : orderOf x = 3) :
    ∃ w y : PSL(2, F), w * x * w⁻¹ = x⁻¹ ∧ y * x = x * y ∧ 3 ∣ orderOf y ∧
      (orderOf y * 2 = Fintype.card F - 1 ∨ orderOf y * 2 = Fintype.card F + 1) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare hF
  have hunip : ∀ t : F, ¬ IsConj x (mk (unip t)) := by
    intro t h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    have hord : orderOf (mk (unip t)) = 3 := by
      rw [← hc, ← hx]
      have := MulEquiv.orderOf_eq (MulAut.conj c) x
      rwa [MulAut.conj_apply] at this
    have hdvd := Subgroup.orderOf_dvd_natCard (unipotent F) (mk_unip_mem_unipotent t)
    rw [hord, card_unipotent h2] at hdvd
    exact h3 hdvd
  rcases conj_cases hF hq hν x with h | h | h | ⟨x₀, hx₀, -, hc⟩ | ⟨x₀, hx₀, -, hc⟩
  · rw [h, orderOf_one] at hx
    norm_num at hx
  · exact (hunip 1 h).elim
  · exact (hunip ν h).elim
  · have := splitTorus_isCyclic (F := F)
    obtain ⟨w, y, hw, hy, hyo, hdvd⟩ := exists_inv_comm_of_isConj_l2odd189 (S := splitTorus F)
      (fun a ha => splitWeyl_conj ha) (fun a ha b hb => splitTorus_mul_comm ha hb) hx₀ hc
    refine ⟨w, y, hw, hy, by rw [hyo, ← hx]; exact hdvd, Or.inl ?_⟩
    rw [hyo]
    exact card_splitTorus h2
  · have := CFSG.QuasithinUnique.K1.nonsplitTorus_isCyclic hν
    obtain ⟨w₀, -, -, hw₀, -⟩ := exists_nonsplitWeyl hF hν
    obtain ⟨w, y, hw, hy, hyo, hdvd⟩ := exists_inv_comm_of_isConj_l2odd189 (S := nonsplitTorus ν)
      hw₀ (fun a ha b hb => nonsplitTorus_mul_comm ha hb) hx₀ hc
    refine ⟨w, y, hw, hy, by rw [hyo, ← hx]; exact hdvd, Or.inr ?_⟩
    rw [hyo]
    exact card_nonsplitTorus hF hν

end CFSG.RankThree.PartTwo.Sec18
