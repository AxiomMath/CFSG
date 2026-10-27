module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Grp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup

theorem w183k3_exists_mul_of_mem_sup {W : Type*} [Group W] {A B : Subgroup W}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : W} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun y _ => ∃ a ∈ A, ∃ b ∈ B, a * b = y)
    ?_ ?_ ?_ ?_ hx
  · rintro y (hy | hy)
    · exact ⟨y, hy, 1, B.one_mem, mul_one y⟩
    · exact ⟨1, A.one_mem, y, hy, one_mul y⟩
  · exact ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
  · rintro _ _ _ _ ⟨a₁, ha₁, b₁, hb₁, rfl⟩ ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    calc (a₁ * a₂) * (b₁ * b₂) = a₁ * ((a₂ * b₁) * b₂) := by group
      _ = a₁ * ((b₁ * a₂) * b₂) := by rw [hcomm a₂ ha₂ b₁ hb₁]
      _ = (a₁ * b₁) * (a₂ * b₂) := by group
  · rintro _ _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    rw [mul_inv_rev]
    exact hcomm a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)

theorem w183k3_odd_card_sup {W : Type*} [Group W] [Finite W] {A B : Subgroup W}
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : Odd (Nat.card ↥A))
    (hB : Odd (Nat.card ↥B)) : Odd (Nat.card ↥(A ⊔ B)) := by
  apply w183k3_odd_card_of_forall
  intro g hg k hk
  obtain ⟨a, ha, b, hb, rfl⟩ := w183k3_exists_mul_of_mem_sup hcomm hg
  have hoa : Odd (orderOf a) := Odd.of_dvd_nat hA (Subgroup.orderOf_dvd_natCard A ha)
  have hob : Odd (orderOf b) := Odd.of_dvd_nat hB (Subgroup.orderOf_dvd_natCard B hb)
  have hcm : Commute a b := hcomm a ha b hb
  have hlcm : Odd (Nat.lcm (orderOf a) (orderOf b)) :=
    Odd.of_dvd_nat (hoa.mul hob) (Nat.lcm_dvd_mul _ _)
  have hodd : Odd (orderOf (a * b)) := Odd.of_dvd_nat hlcm hcm.orderOf_mul_dvd_lcm
  have hcop : (orderOf (a * b)).Coprime (2 ^ k) :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)).symm
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hk))

end CFSG.LocalAnalysis.WeakClosure81

end
