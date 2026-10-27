module

public import CFSG.Sporadic.Recognition.LyonsLocalPreim

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup

section DeltaGen

variable {G : Type*} [Group G]

theorem isConj_inv_of_isConj {a b : G} (hab : IsConj a b) (ha : IsConj a a⁻¹) :
    IsConj a b⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hab
  have : IsConj a⁻¹ (c * a * c⁻¹)⁻¹ := isConj_iff.2 ⟨c, by group⟩
  exact ha.trans this

theorem zpowers_eq_iff {a b : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) :
    zpowers b = zpowers a ↔ b = a ∨ b = a⁻¹ := by
  constructor
  · intro h
    have hb : b ∈ zpowers a := h ▸ mem_zpowers b
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
    rcases zpow_cases ha3 k with hk | hk | hk
    · exfalso
      rw [hk] at h
      apply ha1
      have : a ∈ zpowers (1 : G) := h ▸ mem_zpowers a
      simpa using this
    · exact Or.inl hk
    · refine Or.inr ?_
      rw [hk]
      exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact ha3)
  · rintro (rfl | rfl)
    · rfl
    · exact zpowers_inv

@[expose] def Delta (x : G) : Set (Subgroup G) := {B | ∃ w, IsConj x w ∧ B = zpowers w}

@[expose] def deltaIn (x : G) (K : Subgroup G) : Set (Subgroup G) := {B | B ∈ Delta x ∧ B ≤ K}

theorem mem_deltaIn_iff {x : G} {K B : Subgroup G} :
    B ∈ deltaIn x K ↔ ∃ w, IsConj x w ∧ w ∈ K ∧ B = zpowers w := by
  constructor
  · rintro ⟨⟨w, hw, rfl⟩, hle⟩
    exact ⟨w, hw, hle (mem_zpowers w), rfl⟩
  · rintro ⟨w, hw, hwK, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, (zpowers_le).2 hwK⟩

theorem projQ_self (x : G) :
    projQ x ⟨x, self_mem_centralizer_singleton x⟩ = 1 := by
  rw [projQ_apply, QuotientGroup.eq_one_iff]
  exact mem_zpowers _


end DeltaGen

end CFSG.Sporadic.Recognition.LyonsSims
