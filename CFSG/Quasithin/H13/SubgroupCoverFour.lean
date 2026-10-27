module

public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.FinCases

public section

namespace CFSG.Quasithin.H13.Cover

open scoped Classical

variable {Y : Type*} [Group Y]

noncomputable def sf [Finite Y] (B : Subgroup Y) : Finset Y :=
  (Set.toFinite (B : Set Y)).toFinset

theorem mem_sf [Finite Y] (B : Subgroup Y) (y : Y) : y ∈ sf B ↔ y ∈ B := by
  unfold sf
  simp

theorem card_sf [Finite Y] (B : Subgroup Y) : (sf B).card = Nat.card B := by
  unfold sf
  exact (Nat.card_eq_card_finite_toFinset (Set.toFinite (B : Set Y))).symm

theorem sf_inter [Finite Y] (B C : Subgroup Y) : sf B ∩ sf C = sf (B ⊓ C) := by
  ext y
  simp [mem_sf]

theorem mul_card_le [Finite Y] (B : Subgroup Y) (k : ℕ) (hk : k ≤ B.index) :
    k * Nat.card B ≤ Nat.card Y := by
  rw [← B.card_mul_index, mul_comm k]
  exact Nat.mul_le_mul_left _ hk

theorem card_le_index_mul [Finite Y] (B C : Subgroup Y) :
    Nat.card C ≤ B.index * Nat.card ↥(B ⊓ C) := by
  have h1 : B.relIndex C * Nat.card ↥(B ⊓ C) = Nat.card C := Subgroup.relIndex_mul_card B C
  have h2 : B.relIndex C ≤ B.index := by
    have hi := Subgroup.index_inf (H := B) (K := C)
    have hl := Subgroup.index_inf_le (H := B) (K := C)
    have hC : 0 < C.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    rw [hi] at hl
    exact Nat.le_of_mul_le_mul_right hl hC
  rw [← h1]
  exact Nat.mul_le_mul_right _ h2

theorem union_three_le [Finite Y] (B C D : Subgroup Y) (hB : B.index = 3) (hC : 3 ≤ C.index)
    (hD : 3 ≤ D.index) : 9 * (sf B ∪ sf C ∪ sf D).card ≤ 7 * Nat.card Y := by
  have hg := B.card_mul_index
  have hgC := C.card_mul_index
  have hgD := D.card_mul_index
  have hBC := card_le_index_mul B C
  have hBD := card_le_index_mul B D
  rw [hB] at hBC hBD hg
  have hsub : sf B ∪ sf C ∪ sf D ⊆ sf B ∪ ((sf C \ sf B) ∪ (sf D \ sf B)) := by
    intro y hy
    simp only [Finset.mem_union, Finset.mem_sdiff] at hy ⊢
    by_cases hyB : y ∈ sf B
    · exact Or.inl hyB
    · rcases hy with (h | h) | h
      · exact absurd h hyB
      · exact Or.inr (Or.inl ⟨h, hyB⟩)
      · exact Or.inr (Or.inr ⟨h, hyB⟩)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (sf B) ((sf C \ sf B) ∪ (sf D \ sf B))
  have h3 := Finset.card_union_le (sf C \ sf B) (sf D \ sf B)
  have e1 : (sf C \ sf B).card + (sf C ∩ sf B).card = (sf C).card :=
    Finset.card_sdiff_add_card_inter _ _
  have e2 : (sf D \ sf B).card + (sf D ∩ sf B).card = (sf D).card :=
    Finset.card_sdiff_add_card_inter _ _
  rw [Finset.inter_comm, sf_inter, card_sf, card_sf] at e1 e2
  rw [card_sf] at h2
  have hC3 := mul_card_le C 3 hC
  have hD3 := mul_card_le D 3 hD
  omega

theorem union_three_le' [Finite Y] (B C D : Subgroup Y) (hB : 9 ≤ B.index) (hC : 9 ≤ C.index)
    (hD : 9 ≤ D.index) : 9 * (sf B ∪ sf C ∪ sf D).card ≤ 7 * Nat.card Y := by
  have hg := B.card_mul_index
  have hgC := C.card_mul_index
  have hgD := D.card_mul_index
  have h1 := Finset.card_union_le (sf B ∪ sf C) (sf D)
  have h2 := Finset.card_union_le (sf B) (sf C)
  rw [card_sf] at h1
  rw [card_sf, card_sf] at h2
  have hB9 := mul_card_le B 9 hB
  have hC9 := mul_card_le C 9 hC
  have hD9 := mul_card_le D 9 hD
  omega

theorem not_cover_four [Finite Y] (R : Subgroup Y) (hR : ¬ 2 ∣ R.index) (A : Fin 4 → Subgroup Y)
    (hRA : ∀ i, R ≤ A i) (hne : ∀ i, A i ≠ ⊤) (h3 : ∀ i, 3 ∣ (A i).index)
    (h5 : 5 ∣ (A 0).index) (hcov : ∀ y : Y, ∃ i, y ∈ A i) : False := by
  have : Fintype Y := Fintype.ofFinite Y
  have hodd : ∀ i, ¬ 2 ∣ (A i).index := fun i h2 =>
    hR (h2.trans (Subgroup.index_dvd_of_le (hRA i)))
  have hpos : ∀ i, 0 < (A i).index := fun i =>
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hne1 : ∀ i, (A i).index ≠ 1 := fun i h => hne i (Subgroup.index_eq_one.mp h)
  have hge3 : ∀ i, 3 ≤ (A i).index := fun i => by
    have := h3 i; have := hpos i; have := hne1 i; have := hodd i; omega
  have hge15 : 15 ≤ (A 0).index := by
    have := h3 0; have := h5; have := hpos 0; have := hodd 0; omega
  have hgpos : 0 < Nat.card Y := Nat.card_pos
  have hT : 9 * (sf (A 1) ∪ sf (A 2) ∪ sf (A 3)).card ≤ 7 * Nat.card Y := by
    by_cases c1 : (A 1).index = 3
    · exact union_three_le (A 1) (A 2) (A 3) c1 (hge3 2) (hge3 3)
    by_cases c2 : (A 2).index = 3
    · have := union_three_le (A 2) (A 1) (A 3) c2 (hge3 1) (hge3 3)
      rwa [Finset.union_comm (sf (A 2)) (sf (A 1))] at this
    by_cases c3 : (A 3).index = 3
    · have := union_three_le (A 3) (A 1) (A 2) c3 (hge3 1) (hge3 2)
      have e : sf (A 3) ∪ sf (A 1) ∪ sf (A 2) = sf (A 1) ∪ sf (A 2) ∪ sf (A 3) := by
        ext y; simp only [Finset.mem_union]; tauto
      rwa [e] at this
    have n1 : 9 ≤ (A 1).index := by
      have := h3 1; have := hpos 1; have := hodd 1; omega
    have n2 : 9 ≤ (A 2).index := by
      have := h3 2; have := hpos 2; have := hodd 2; omega
    have n3 : 9 ≤ (A 3).index := by
      have := h3 3; have := hpos 3; have := hodd 3; omega
    exact union_three_le' _ _ _ n1 n2 n3
  have hcovF : (Finset.univ : Finset Y) ⊆ sf (A 0) ∪ (sf (A 1) ∪ sf (A 2) ∪ sf (A 3)) := by
    intro y _
    obtain ⟨i, hi⟩ := hcov y
    simp only [Finset.mem_union, mem_sf]
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl (Or.inl hi))
    · exact Or.inr (Or.inl (Or.inr hi))
    · exact Or.inr (Or.inr hi)
  have h1 := Finset.card_le_card hcovF
  have h2 := Finset.card_union_le (sf (A 0)) (sf (A 1) ∪ sf (A 2) ∪ sf (A 3))
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  rw [card_sf] at h2
  have hg0 := (A 0).card_mul_index
  have h15 := mul_card_le (A 0) 15 hge15
  omega

end CFSG.Quasithin.H13.Cover
