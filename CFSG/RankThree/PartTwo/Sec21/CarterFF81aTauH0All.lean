module

import CFSG.RankThree.PartTwo.Sec21.FF81S0
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec32

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.exists_inverting_involution_of_inverting (h : FF81Hyp b L)
    {b₁ b₂ b₃ n : G} (hnL : n ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hself : L ⊓ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set G)) =
      Subgroup.closure ({b₁, b₂, b₃} : Set G))
    (hn₁ : n * b₁ * n⁻¹ = b₁⁻¹) (hn₂ : n * b₂ * n⁻¹ = b₂⁻¹) (hn₃ : n * b₃ * n⁻¹ = b₃⁻¹) :
    ∃ τ : G, τ ∈ L ∧ orderOf τ = 2 ∧ τ * b * τ⁻¹ = b ∧
      τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹ := by
  have hnb : n * b * n⁻¹ = b := by
    have hcb : Commute n b := Subgroup.mem_centralizer_singleton_iff.mp (h.hLC hnL)
    rw [hcb.eq, mul_assoc, mul_inv_cancel, mul_one]
  set B₁ : Subgroup G := Subgroup.closure ({b₁, b₂, b₃} : Set G) with hB₁
  have hB₁_card : Nat.card B₁ = 27 := by
    simpa [hB₁] using hE.2
  have hB₁_ne_bot : B₁ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hB₁_card
    norm_num at hB₁_card
  have hcomm : ∀ x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G),
      ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), x * y = y * x :=
    fun x hx y hy => comm_of_isElemAb hE x hx y hy
  have hinvB : ∀ x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), n * x * n⁻¹ = x⁻¹ :=
    fun x hx => conj_eq_inv_of_closure hcomm (by
      rintro x (rfl | rfl | rfl)
      exacts [hn₁, hn₂, hn₃]) hx
  have hn2C : n ^ 2 ∈ CenS B₁ := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : n * y * n⁻¹ = y⁻¹ := hinvB y hy
    have h2 : n ^ 2 * y * (n ^ 2)⁻¹ = y := by
      have h2' : n ^ 2 = n * n := by rw [pow_two]
      calc n ^ 2 * y * (n ^ 2)⁻¹ = n * (n * y * n⁻¹) * n⁻¹ := by
            rw [h2', mul_inv_rev]
            group
        _ = n * y⁻¹ * n⁻¹ := by rw [h1]
        _ = (n * y * n⁻¹)⁻¹ := by group
        _ = (y⁻¹)⁻¹ := by rw [h1]
        _ = y := by group
    calc y * n ^ 2 = (n ^ 2 * y * (n ^ 2)⁻¹) * n ^ 2 := by rw [h2]
      _ = n ^ 2 * y := by group
  have hn2B₁ : n ^ 2 ∈ B₁ := by
    have hmem : n ^ 2 ∈ L ⊓ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set G)) :=
      ⟨L.pow_mem hnL 2, hn2C⟩
    rwa [hself] at hmem
  have hn6 : n ^ 6 = 1 := by
    have h := pow_three_eq_one_of_isElemAb hE hn2B₁
    rw [show n ^ 6 = (n ^ 2) ^ 3 by rw [← pow_mul]]
    exact h
  have hbot_of_inv : ∀ i : G, i ∈ B₁ → (∀ x ∈ B₁, i * x * i⁻¹ = x⁻¹) → B₁ = ⊥ := by
    intro i hi hinvi
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [Subgroup.mem_bot]
    have hxi : Commute i x := hcomm i hi x hx
    have hxfix : i * x * i⁻¹ = x := by
      rw [hxi.eq, mul_assoc, mul_inv_cancel, mul_one]
    have hx_eq_inv : x = x⁻¹ := hxfix.symm.trans (hinvi x hx)
    have hx2 : x ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp hx_eq_inv
    have hx3 : x ^ 3 = 1 := pow_three_eq_one_of_isElemAb hE hx
    calc x = x ^ 3 * (x ^ 2)⁻¹ := by
          rw [show x ^ 3 = x * x ^ 2 by rw [pow_succ']]
          group
      _ = 1 := by rw [hx3, hx2, inv_one, mul_one]
  by_cases hn2one : n ^ 2 = 1
  · refine ⟨n, hnL, orderOf_eq_prime hn2one ?_, hnb, hn₁, hn₂, hn₃⟩
    intro hn
    have hinv1 : ∀ x ∈ B₁, (1 : G) * x * 1⁻¹ = x⁻¹ := by
      intro x hx
      simpa [hn] using hinvB x hx
    exact hB₁_ne_bot (hbot_of_inv 1 B₁.one_mem hinv1)
  · have hn3ne : n ^ 3 ≠ 1 := by
      intro h3
      have h3' : n * n ^ 2 = 1 := by
        rw [show n * n ^ 2 = n ^ 3 by group]
        exact h3
      have hn_eq : n = (n ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h3'
      have hnB₁ : n ∈ B₁ := by
        rw [hn_eq]
        exact B₁.inv_mem hn2B₁
      exact hB₁_ne_bot (hbot_of_inv n hnB₁ hinvB)
    have hτ2 : (n ^ 3) ^ 2 = 1 := by
      calc (n ^ 3) ^ 2 = n ^ 6 := by rw [← pow_mul]
        _ = 1 := hn6
    have hτinvB : ∀ x ∈ B₁, n ^ 3 * x * (n ^ 3)⁻¹ = x⁻¹ := by
      intro x hx
      have h1 : n * x * n⁻¹ = x⁻¹ := hinvB x hx
      have h2 : n ^ 2 * x * (n ^ 2)⁻¹ = x := by
        have hc : Commute (n ^ 2) x := hcomm (n ^ 2) (by simpa [hB₁] using hn2B₁) x
          (by simpa [hB₁] using hx)
        rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
      calc n ^ 3 * x * (n ^ 3)⁻¹
          = n * (n ^ 2 * x * (n ^ 2)⁻¹) * n⁻¹ := by
              rw [show n ^ 3 = n * n ^ 2 by rw [pow_succ'], mul_inv_rev]
              group
        _ = n * x * n⁻¹ := by rw [h2]
        _ = x⁻¹ := h1
    have hτb : n ^ 3 * b * (n ^ 3)⁻¹ = b := by
      have hcb : Commute n b := by
        rw [commute_iff_eq]
        calc n * b = (n * b * n⁻¹) * n := by group
          _ = b * n := by rw [hnb]
      have hcb3 : Commute (n ^ 3) b := hcb.pow_left 3
      calc n ^ 3 * b * (n ^ 3)⁻¹ = b * n ^ 3 * (n ^ 3)⁻¹ := by rw [hcb3.eq]
        _ = b := by rw [mul_assoc, mul_inv_cancel, mul_one]
    refine ⟨n ^ 3, L.pow_mem hnL 3, orderOf_eq_prime hτ2 hn3ne, hτb, ?_, ?_, ?_⟩
    · exact hτinvB b₁ (Subgroup.subset_closure (by simp))
    · exact hτinvB b₂ (Subgroup.subset_closure (by simp))
    · exact hτinvB b₃ (Subgroup.subset_closure (by simp))

end CFSG.RankThree.PartTwo.Sec21.FF81
