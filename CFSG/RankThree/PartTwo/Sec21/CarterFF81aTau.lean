module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec32
import CFSG.RankThree.PartTwo.Sec21.FF81S0
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.cen_B_inverting_involution (h : FF81Hyp b L)
    {τ : G} (hτL : τ ∈ L) (hτ2 : orderOf τ = 2)
    {b₁ b₂ b₃ : G} (hb₁ : b₁ ∈ L) (hb₂ : b₂ ∈ L) (hb₃ : b₃ ∈ L)
    (hE : IsElemAb 3 3 (Subgroup.closure ({b₁, b₂, b₃} : Set G)))
    (hinv : τ * b₁ * τ⁻¹ = b₁⁻¹ ∧ τ * b₂ * τ⁻¹ = b₂⁻¹ ∧ τ * b₃ * τ⁻¹ = b₃⁻¹) :
    Subgroup.closure ({b, b₁, b₂, b₃} : Set G) ⊓ Cen τ =
      Subgroup.zpowers b := by
  have hB_eq : Subgroup.closure ({b, b₁, b₂, b₃} : Set G) =
      Subgroup.zpowers b ⊔ Subgroup.closure ({b₁, b₂, b₃} : Set G) :=
    closure_four_eq b b₁ b₂ b₃
  have hcomm : ∀ x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G),
      ∀ y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), x * y = y * x :=
    fun x hx y hy => comm_of_isElemAb hE x hx y hy
  have hinv' : ∀ x ∈ ({b₁, b₂, b₃} : Set G), τ * x * τ⁻¹ = x⁻¹ := by
    rintro x (rfl | rfl | rfl)
    exacts [hinv.1, hinv.2.1, hinv.2.2]
  have hinvB : ∀ x ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G), τ * x * τ⁻¹ = x⁻¹ :=
    fun x hx => conj_eq_inv_of_closure hcomm hinv' hx
  have hB₁L : Subgroup.closure ({b₁, b₂, b₃} : Set G) ≤ L :=
    (Subgroup.closure_le L).mpr (by
      rintro x (rfl | rfl | rfl)
      exacts [hb₁, hb₂, hb₃])
  have hbC : b ∈ CenS (Subgroup.closure ({b₁, b₂, b₃} : Set G)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (h.hLC (hB₁L hx))
  have hbN : Subgroup.zpowers b ≤ Subgroup.normalizer
      (Subgroup.closure ({b₁, b₂, b₃} : Set G) : Set G) :=
    (Subgroup.zpowers_le.mpr hbC).trans
      (Subgroup.centralizer_le_normalizer (Subgroup.closure ({b₁, b₂, b₃} : Set G) : Set G))
  have hcoe : (↑(Subgroup.zpowers b ⊔ Subgroup.closure ({b₁, b₂, b₃} : Set G)) : Set G) =
      (Subgroup.zpowers b : Set G) * (Subgroup.closure ({b₁, b₂, b₃} : Set G) : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers b)
      (Subgroup.closure ({b₁, b₂, b₃} : Set G)) hbN
  have hτb : Commute τ b := Subgroup.mem_centralizer_singleton_iff.mp (h.hLC hτL)
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxB, hxC⟩ := hx
    rw [hB_eq] at hxB
    change x ∈ ((Subgroup.zpowers b ⊔ Subgroup.closure ({b₁, b₂, b₃} : Set G) :
      Subgroup G) : Set G) at hxB
    rw [hcoe, Set.mem_mul] at hxB
    obtain ⟨a, ha, c, hc, hxac⟩ := hxB
    rw [← hxac] at hxC ⊢
    have hτa : Commute τ a := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      exact hτb.zpow_right k
    have hτac : Commute τ (a * c) := (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm
    have hτc : Commute τ c := by
      have h : Commute τ (a⁻¹ * (a * c)) := hτa.inv_right.mul_right hτac
      rwa [inv_mul_cancel_left] at h
    have hc_eq_inv : c = c⁻¹ := by
      have hfix : τ * c * τ⁻¹ = c := by
        rw [hτc.eq, mul_assoc, mul_inv_cancel, mul_one]
      exact hfix.symm.trans (hinvB c hc)
    have hc2 : c ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp hc_eq_inv
    have hc3 : c ^ 3 = 1 := pow_three_eq_one_of_isElemAb hE hc
    have hc1 : c = 1 := by
      calc c = c ^ 3 * (c ^ 2)⁻¹ := by
            rw [show c ^ 3 = c * c ^ 2 by rw [pow_succ']]
            group
        _ = 1 := by rw [hc3, hc2, inv_one, mul_one]
    rw [hc1, mul_one]
    exact ha
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [hB_eq]
      exact Subgroup.mem_sup_left hx
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      change b ^ k ∈ Subgroup.centralizer ({τ} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (hτb.zpow_right k).eq

end CFSG.RankThree.PartTwo.Sec21.FF81
