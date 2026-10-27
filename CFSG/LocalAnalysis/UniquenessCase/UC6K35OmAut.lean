module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)

theorem comm_of_central_index_prime {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    {S B : Subgroup Y} (hBS : B ≤ S) (hBc : ∀ b ∈ B, ∀ y ∈ S, b * y = y * b)
    (hcard : Nat.card S = p * Nat.card B) : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
  set N : Subgroup ↥S := B.subgroupOf S
  have hNc : N ≤ Subgroup.center ↥S := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (hBc n (Subgroup.mem_subgroupOf.1 hn) s s.2).symm
  haveI : N.Normal := ⟨fun n hn s => by
    have h := Subgroup.mem_center_iff.1 (hNc hn) s
    rw [h, mul_inv_cancel_right]
    exact hn⟩
  have hNcard : Nat.card N = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv
  have hq : Nat.card (↥S ⧸ N) = p := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hNcard, hcard] at h
    have hB0 : 0 < Nat.card B := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hB0 h).symm
  haveI : IsCyclic (↥S ⧸ N) := isCyclic_of_prime_card hq
  intro x hx y hy
  have h := commutative_of_cyclic_center_quotient (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk']; exact hNc) ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val h

end CFSG.LocalAnalysis.UniquenessCase.UCK
