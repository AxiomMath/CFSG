module

public import CFSG.Quasithin.H13.GoldschmidtI51GQFin
public import CFSG.Quasithin.H13.GoldschmidtI51Conj
public import CFSG.Quasithin.H13.GoldschmidtI51ModelsA6

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Quasithin.H13.A6 Equiv

@[expose] def sgR (b : Bool) : Subgroup (Perm (Fin 6)) := if b then A6g else ⊤

@[expose] def sgA (b o : Bool) : Subgroup (Perm (Fin 6)) :=
  (if o then P1sub else P2sub) ⊓ sgR b

@[expose] def sgB (b o : Bool) : Subgroup (Perm (Fin 6)) :=
  (if o then P2sub else P1sub) ⊓ sgR b

theorem mem_sgR {b : Bool} {σ : Perm (Fin 6)} : σ ∈ sgR b ↔ InR b σ := by
  cases b <;> simp [sgR, InR, Equiv.Perm.mem_alternatingGroup]

theorem mem_sgA {b o : Bool} {σ : Perm (Fin 6)} : σ ∈ sgA b o ↔ InR b σ ∧ InA o σ := by
  cases o <;> simp [sgA, InA, mem_sgR, mem_P1sub, mem_P2sub, and_comm]

theorem mem_sgB {b o : Bool} {σ : Perm (Fin 6)} : σ ∈ sgB b o ↔ InR b σ ∧ InB o σ := by
  cases o <;> simp [sgB, InB, mem_sgR, mem_P1sub, mem_P2sub, and_comm]

theorem sgA_le_sgR (b o : Bool) : sgA b o ≤ sgR b := fun _ h => mem_sgR.2 (mem_sgA.1 h).1

theorem sgB_le_sgR (b o : Bool) : sgB b o ≤ sgR b := fun _ h => mem_sgR.2 (mem_sgB.1 h).1

theorem nn_mem_R (b o : Bool) : nn o ∈ sgR b := mem_sgR.2 (Or.inr (fin_nn o).2.2.1)

theorem ff_mem_R (b o : Bool) : ff o ∈ sgR b := mem_sgR.2 (Or.inr (fin_nn o).2.2.2)

theorem nn_mem_B (b o : Bool) : nn o ∈ sgB b o := mem_sgB.2 ⟨mem_sgR.1 (nn_mem_R b o), (fin_nn o).1⟩

theorem nn_not_mem_A (b o : Bool) : nn o ∉ sgA b o := fun h => (fin_nn o).2.1 (mem_sgA.1 h).2

theorem ff_not_mem_A (b o : Bool) : ff o ∉ sgA b o := fun h => (fin_ff o).1 (mem_sgA.1 h).2

theorem ff_not_mem_AnA (b o : Bool) {a a' : Perm (Fin 6)} (ha : a ∈ sgA b o) (ha' : a' ∈ sgA b o) :
    ff o ≠ a * nn o * a' := by
  intro h
  have := (fin_ff o).2 a (mem_sgA.1 ha).2
  apply this
  have e : (a * nn o)⁻¹ * ff o = a' := by rw [h]; group
  rw [e]; exact (mem_sgA.1 ha').2

theorem gq_cover (b o : Bool) {σ : Perm (Fin 6)} (hσ : σ ∈ sgR b) :
    σ ∈ sgA b o ∨ (∃ a ∈ sgA b o, ∃ a' ∈ sgA b o, σ = a * nn o * a') ∨
      (∃ a ∈ sgA b o, ∃ a' ∈ sgA b o, σ = a * ff o * a') := by
  rcases fin_cover b o σ (mem_sgR.1 hσ) with h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩
  · exact Or.inl (mem_sgA.2 ⟨mem_sgR.1 hσ, h⟩)
  · have haA : a ∈ sgA b o := mem_sgA.2 ((fin_sound b o).1 a ha)
    have hR : (a * nn o)⁻¹ * σ ∈ sgR b :=
      (sgR b).mul_mem ((sgR b).inv_mem ((sgR b).mul_mem (sgA_le_sgR b o haA) (nn_mem_R b o))) hσ
    refine Or.inr (Or.inl ⟨a, haA, _, mem_sgA.2 ⟨mem_sgR.1 hR, h⟩, by group⟩)
  · have haA : a ∈ sgA b o := mem_sgA.2 ((fin_sound b o).1 a ha)
    have hR : (a * ff o)⁻¹ * σ ∈ sgR b :=
      (sgR b).mul_mem ((sgR b).inv_mem ((sgR b).mul_mem (sgA_le_sgR b o haA) (ff_mem_R b o))) hσ
    refine Or.inr (Or.inr ⟨a, haA, _, mem_sgA.2 ⟨mem_sgR.1 hR, h⟩, by group⟩)

theorem gq_BsubA (b o : Bool) {σ : Perm (Fin 6)} (hσ : σ ∈ sgB b o) :
    σ ∈ sgA b o ∨ ∃ a ∈ sgA b o, ∃ a' ∈ sgA b o, σ = a * nn o * a' := by
  have hσR : σ ∈ sgR b := sgB_le_sgR b o hσ
  rcases fin_BsubA b o σ (mem_sgB.1 hσ).1 (mem_sgB.1 hσ).2 with h | ⟨a, ha, h⟩
  · exact Or.inl (mem_sgA.2 ⟨mem_sgR.1 hσR, h⟩)
  · have haA : a ∈ sgA b o := mem_sgA.2 ((fin_sound b o).1 a ha)
    have hR : (a * nn o)⁻¹ * σ ∈ sgR b :=
      (sgR b).mul_mem ((sgR b).inv_mem ((sgR b).mul_mem (sgA_le_sgR b o haA) (nn_mem_R b o))) hσR
    exact Or.inr ⟨a, haA, _, mem_sgA.2 ⟨mem_sgR.1 hR, h⟩, by group⟩

theorem gq_gq3 (b o : Bool) {a : Perm (Fin 6)} (ha : a ∈ sgA b o) :
    ∃ c ∈ sgB b o, c⁻¹ * a * ff o ∈ sgA b o ∨
      ∃ a' ∈ sgA b o, ∃ a'' ∈ sgA b o, c⁻¹ * a * ff o = a' * nn o * a'' := by
  have haL : a ∈ LA b o := fin_LA_complete b o a (mem_sgA.1 ha).1 (mem_sgA.1 ha).2
  obtain ⟨c, hc, h⟩ := fin_gq3 b o a haL
  have hcB : c ∈ sgB b o := mem_sgB.2 ((fin_sound b o).2.1 c hc)
  refine ⟨c, hcB, ?_⟩
  have hx : c⁻¹ * a * ff o ∈ sgR b :=
    (sgR b).mul_mem ((sgR b).mul_mem ((sgR b).inv_mem (sgB_le_sgR b o hcB)) (sgA_le_sgR b o ha))
      (ff_mem_R b o)
  rcases h with h | ⟨a', ha', h⟩
  · exact Or.inl (mem_sgA.2 ⟨mem_sgR.1 hx, h⟩)
  · have ha'A : a' ∈ sgA b o := mem_sgA.2 ((fin_sound b o).1 a' ha')
    have hR : (a' * nn o)⁻¹ * (c⁻¹ * a * ff o) ∈ sgR b :=
      (sgR b).mul_mem ((sgR b).inv_mem ((sgR b).mul_mem (sgA_le_sgR b o ha'A) (nn_mem_R b o))) hx
    exact Or.inr ⟨a', ha'A, _, mem_sgA.2 ⟨mem_sgR.1 hR, h⟩, by group⟩

theorem gq_core (b o : Bool) {n : Perm (Fin 6)} (hn : n ∈ sgR b)
    (h : ∀ g ∈ sgR b, g⁻¹ * n * g ∈ sgA b o) : n = 1 := by
  refine fin_core b o n (mem_sgR.1 hn) (fun s hs => ?_)
  have hsR : s ∈ sgR b := mem_sgR.2 (Or.inr (by
    have := (fin_sound b o).2.2 s hs
    rcases this with h | h
    · exact absurd h (by decide)
    · exact h))
  exact (mem_sgA.1 (h s hsR)).2

theorem natCard_sgR (b : Bool) :
    Nat.card ↥(sgR b) = Fintype.card {σ : Perm (Fin 6) // InR b σ} := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => mem_sgR)

theorem natCard_sgA (b o : Bool) :
    Nat.card ↥(sgA b o) = Fintype.card {σ : Perm (Fin 6) // InR b σ ∧ InA o σ} := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => mem_sgA)

theorem natCard_sgB (b o : Bool) :
    Nat.card ↥(sgB b o) = Fintype.card {σ : Perm (Fin 6) // InR b σ ∧ InB o σ} := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => mem_sgB)

theorem relIndex_sgA (b o : Bool) : (sgA b o).relIndex (sgR b) = 15 := by
  have h := Subgroup.relIndex_mul_card (H := sgA b o) (K := sgR b)
  rw [inf_eq_left.2 (sgA_le_sgR b o)] at h
  have h2 : Nat.card ↥(sgR b) = 15 * Nat.card ↥(sgA b o) := by
    rw [natCard_sgR, natCard_sgA]; exact (fin_card b o).1
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem relIndex_sgB (b o : Bool) : (sgB b o).relIndex (sgR b) = 15 := by
  have h := Subgroup.relIndex_mul_card (H := sgB b o) (K := sgR b)
  rw [inf_eq_left.2 (sgB_le_sgR b o)] at h
  have h2 : Nat.card ↥(sgR b) = 15 * Nat.card ↥(sgB b o) := by
    rw [natCard_sgR, natCard_sgB]; exact (fin_card b o).2
  rw [h2] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h

theorem mem_inf_cj_sgA {b o : Bool} {g σ : Perm (Fin 6)} (hg : g ∈ sgR b) :
    σ ∈ sgA b o ⊓ cj g (sgA b o) ↔ InR b σ ∧ InA o σ ∧ InA o (g⁻¹ * σ * g) := by
  rw [Subgroup.mem_inf, mem_cj, mem_sgA, mem_sgA]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, ?_, h3⟩
    exact mem_sgR.1 ((sgR b).mul_mem ((sgR b).mul_mem ((sgR b).inv_mem hg) (mem_sgR.2 h1)) hg)

theorem relIndex_far (b o : Bool) :
    (sgA b o ⊓ cj (ff o) (sgA b o)).relIndex (sgA b o) = 8 := by
  have h := Subgroup.relIndex_mul_card (H := sgA b o ⊓ cj (ff o) (sgA b o)) (K := sgA b o)
  rw [inf_eq_left.2 inf_le_left] at h
  have hc : Nat.card ↥(sgA b o ⊓ cj (ff o) (sgA b o)) * 8 = Nat.card ↥(sgA b o) := by
    rw [natCard_sgA, ← fin_far_idx b o, ← Nat.card_eq_fintype_card]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => mem_inf_cj_sgA (ff_mem_R b o))
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(sgA b o ⊓ cj (ff o) (sgA b o)))) ?_
  rw [h, ← hc, mul_comm]

theorem relIndex_near (b o : Bool) :
    (sgA b o ⊓ cj (nn o) (sgA b o)).relIndex (sgA b o) = 6 := by
  have h := Subgroup.relIndex_mul_card (H := sgA b o ⊓ cj (nn o) (sgA b o)) (K := sgA b o)
  rw [inf_eq_left.2 inf_le_left] at h
  have hc : Nat.card ↥(sgA b o ⊓ cj (nn o) (sgA b o)) * 6 = Nat.card ↥(sgA b o) := by
    rw [natCard_sgA, ← fin_near_idx b o, ← Nat.card_eq_fintype_card]
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun σ => mem_inf_cj_sgA (nn_mem_R b o))
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥(sgA b o ⊓ cj (nn o) (sgA b o)))) ?_
  rw [h, ← hc, mul_comm]

theorem gq_near_iff (b o : Bool) {σ : Perm (Fin 6)} :
    (∃ a ∈ sgA b o, ∃ β ∈ sgB b o, ∃ c ∈ sgA b o, σ = a * β * c) ↔
      σ ∈ sgA b o ∨ ∃ a ∈ sgA b o, ∃ a' ∈ sgA b o, σ = a * nn o * a' := by
  constructor
  · rintro ⟨a, ha, β, hβ, c, hc, rfl⟩
    rcases gq_BsubA b o hβ with h | ⟨a₀, ha₀, a₁, ha₁, rfl⟩
    · exact Or.inl ((sgA b o).mul_mem ((sgA b o).mul_mem ha h) hc)
    · exact Or.inr ⟨a * a₀, (sgA b o).mul_mem ha ha₀, a₁ * c, (sgA b o).mul_mem ha₁ hc, by group⟩
  · rintro (h | ⟨a, ha, a', ha', rfl⟩)
    · exact ⟨σ, h, 1, (sgB b o).one_mem, 1, (sgA b o).one_mem, by group⟩
    · exact ⟨a, ha, nn o, nn_mem_B b o, a', ha', rfl⟩

theorem gq_far_cover (b o : Bool) {σ : Perm (Fin 6)} (hσ : σ ∈ sgR b)
    (hfar : ¬ ∃ a ∈ sgA b o, ∃ β ∈ sgB b o, ∃ c ∈ sgA b o, σ = a * β * c) :
    ∃ a ∈ sgA b o, ∃ a' ∈ sgA b o, σ = a * ff o * a' := by
  rw [gq_near_iff] at hfar
  rcases gq_cover b o hσ with h | h | h
  · exact absurd (Or.inl h) hfar
  · exact absurd (Or.inr h) hfar
  · exact h

theorem ff_far (b o : Bool) :
    ¬ ∃ a ∈ sgA b o, ∃ β ∈ sgB b o, ∃ c ∈ sgA b o, ff o = a * β * c := by
  rw [gq_near_iff]
  rintro (h | ⟨a, ha, a', ha', h⟩)
  · exact ff_not_mem_A b o h
  · exact ff_not_mem_AnA b o ha ha' h

end CFSG.Quasithin.H13.I51
