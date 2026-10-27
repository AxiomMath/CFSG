module

public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card

public section

namespace CFSG.Quasithin.H13.GM22

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_mul_set_mul_card_inf (A B : Subgroup G) :
    Nat.card ((A : Set G) * (B : Set G)) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient B (A : Set G)
  have h2 : Nat.card (MulAction.orbit ↥A (((1 : G) : G ⧸ B))) *
      Nat.card (MulAction.stabilizer ↥A (((1 : G) : G ⧸ B))) = Nat.card ↥A := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥A _)
  have hset : ((A : Set G).image (QuotientGroup.mk : G → G ⧸ B)) =
      MulAction.orbit ↥A (((1 : G) : G ⧸ B)) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, by simp [Subgroup.smul_def]⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, by simp [Subgroup.smul_def]⟩
  have hstab : Nat.card ↥(MulAction.stabilizer ↥A (((1 : G) : G ⧸ B))) =
      Nat.card ↥(A ⊓ B) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨(a.1 : G), a.1.2, ?_⟩
        invFun := fun x => ⟨⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · obtain ⟨a, ha⟩ := a
      have := MulAction.mem_stabilizer_iff.mp ha
      simpa [Subgroup.smul_def, QuotientGroup.eq] using this
    · rw [MulAction.mem_stabilizer_iff]
      simpa [Subgroup.smul_def, QuotientGroup.eq] using (Subgroup.mem_inf.mp x.2).2
  rw [h1, hset, ← h2, ← hstab]
  ac_rfl

theorem exists_mul_eq_of_card_mul {A B D : Subgroup G} (hA : A ≤ D) (hB : B ≤ D)
    (hcard : Nat.card A * Nat.card B = Nat.card ↥(A ⊓ B) * Nat.card D) :
    ∀ d ∈ D, ∃ a ∈ A, ∃ b ∈ B, d = a * b := by
  have hpos : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
  have h1 := card_mul_set_mul_card_inf A B
  have h2 : Nat.card ((A : Set G) * (B : Set G)) = Nat.card D :=
    Nat.eq_of_mul_eq_mul_right hpos ((h1.trans hcard).trans (mul_comm _ _))
  have hsub : (A : Set G) * (B : Set G) ⊆ (D : Set G) := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact D.mul_mem (hA ha) (hB hb)
  have heq : (A : Set G) * (B : Set G) = (D : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact h2.ge
  intro d hd
  have : d ∈ (A : Set G) * (B : Set G) := heq ▸ hd
  obtain ⟨a, ha, b, hb, rfl⟩ := this
  exact ⟨a, ha, b, hb, rfl⟩

end CFSG.Quasithin.H13.GM22
