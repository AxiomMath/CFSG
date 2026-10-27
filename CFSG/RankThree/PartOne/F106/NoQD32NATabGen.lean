module

public import CFSG.RankThree.PartOne.F106.NoQD32NAGen

public section

namespace CFSG.RankThree.PartOne.F106

open Subgroup

structure GTab (G : Type*) [Group G] where
  sel : ℕ → G
  S : Subgroup G
  card : Nat.card S = 3 ^ 6
  sel_mem : ∀ i < 729, sel i ∈ S
  exists_sel : ∀ y ∈ S, ∃ i < 729, y = sel i
  sel_inj : ∀ i < 729, ∀ j < 729, sel i = sel j → i = j
  sel_zero : sel 0 = 1

section Cover

variable {G : Type*} [Group G] [Finite G]

theorem le_of_cover_three {Y A B C : Subgroup G} {j : ℕ} (hY : Nat.card Y = 3 ^ j)
    (hcov : ∀ y ∈ Y, y ∈ A ∨ y ∈ B ∨ y ∈ C) : Y ≤ A ∨ Y ≤ B ∨ Y ≤ C := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB, hC⟩ := hcon
  have hj : 1 ≤ j := by
    by_contra hj0
    have h1 : Nat.card Y = 1 := by rw [hY, show j = 0 by omega]; rfl
    have hbot : Y = ⊥ := Subgroup.card_eq_one.mp h1
    exact hA (by rw [hbot]; exact bot_le)
  have hproper : ∀ {D : Subgroup G}, ¬ Y ≤ D → Nat.card (Y ⊓ D : Subgroup G) ≤ 3 ^ (j - 1) := by
    intro D hD
    have hlt : (Y ⊓ D : Subgroup G) ≠ Y := fun h => hD (h ▸ inf_le_right)
    exact card_le_of_lt inf_le_left hlt hY
  have hncard : ∀ H : Subgroup G, (H : Set G).ncard = Nat.card H := fun H =>
    (Nat.card_coe_set_eq (H : Set G)).symm
  have hsub : (Y : Set G) ⊆ ((Y ⊓ A : Subgroup G) : Set G) ∪
      (((Y ⊓ B : Subgroup G) : Set G) \ {1}) ∪ (((Y ⊓ C : Subgroup G) : Set G) \ {1}) := by
    intro y hy
    have hyA : y ∈ A → y ∈ ((Y ⊓ A : Subgroup G) : Set G) := fun h => Subgroup.mem_inf.2 ⟨hy, h⟩
    by_cases hy1 : y = 1
    · left
      left
      rw [hy1]
      exact (Y ⊓ A).one_mem
    · rcases hcov y hy with h | h | h
      · exact Or.inl (Or.inl (hyA h))
      · exact Or.inl (Or.inr ⟨Subgroup.mem_inf.2 ⟨hy, h⟩, hy1⟩)
      · exact Or.inr ⟨Subgroup.mem_inf.2 ⟨hy, h⟩, hy1⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (((Y ⊓ A : Subgroup G) : Set G) ∪
      (((Y ⊓ B : Subgroup G) : Set G) \ {1})) (((Y ⊓ C : Subgroup G) : Set G) \ {1})
  have h3 := Set.ncard_union_le ((Y ⊓ A : Subgroup G) : Set G)
    (((Y ⊓ B : Subgroup G) : Set G) \ {1})
  have h4 : (((Y ⊓ B : Subgroup G) : Set G) \ {1}).ncard = Nat.card (Y ⊓ B : Subgroup G) - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Y ⊓ B).one_mem, hncard]
  have h5 : (((Y ⊓ C : Subgroup G) : Set G) \ {1}).ncard = Nat.card (Y ⊓ C : Subgroup G) - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Y ⊓ C).one_mem, hncard]
  have hpB : 0 < Nat.card (Y ⊓ B : Subgroup G) := Nat.card_pos
  have hpC : 0 < Nat.card (Y ⊓ C : Subgroup G) := Nat.card_pos
  rw [hncard Y, hY] at h1
  rw [hncard] at h3
  have hA' := hproper hA
  have hB' := hproper hB
  have hC' := hproper hC
  have hpow : 3 ^ j = 3 * 3 ^ (j - 1) := by
    rw [← pow_succ' 3 (j - 1), Nat.sub_add_cancel hj]
  have hpos : 0 < 3 ^ (j - 1) := by positivity
  omega

end Cover

section Table

variable {G : Type*} [Group G] [Finite G] (T : GTab G)

theorem GTab.exists_subgroup (P : ℕ → Prop) (h0 : P 0)
    (hmul : ∀ i < 729, ∀ j < 729, ∀ k < 729, T.sel i * T.sel j = T.sel k → P i → P j → P k) :
    ∃ H : Subgroup G, H ≤ T.S ∧ ∀ i < 729, T.sel i ∈ H ↔ P i := by
  let L : Set G := {g | ∃ i < 729, P i ∧ g = T.sel i}
  have h1 : (1 : G) ∈ L := ⟨0, by norm_num, h0, T.sel_zero.symm⟩
  have hL : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L := by
    rintro _ ⟨i, hi, hPi, rfl⟩ _ ⟨j, hj, hPj, rfl⟩
    obtain ⟨k, hk, hkeq⟩ := T.exists_sel _ (T.S.mul_mem (T.sel_mem i hi) (T.sel_mem j hj))
    exact ⟨k, hk, hmul i hi j hj k hk hkeq hPi hPj, hkeq⟩
  refine ⟨Subgroup.closure L, ?_, fun i hi => ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, -, rfl⟩
    exact T.sel_mem i hi
  · rw [mem_closure_iff_of_mul_closed h1 hL]
    constructor
    · rintro ⟨j, hj, hPj, hij⟩
      rwa [T.sel_inj i hi j hj hij]
    · intro hP
      exact ⟨i, hi, hP, rfl⟩

omit [Finite G] in
open scoped _root_.Classical in
theorem GTab.card_eq (H : Subgroup G) (hH : H ≤ T.S) :
    Nat.card H = ((Finset.range 729).filter fun i => T.sel i ∈ H).card :=
  card_eq_filter T.S H T.sel T.sel_inj T.exists_sel hH

open scoped _root_.Classical in
theorem GTab.eq_of_elemAbelian {E₀ : Subgroup G} (hE₀ : Nat.card E₀ = 81)
    (huniq : ∀ i < 729, T.sel i ^ 3 = 1 → T.sel i ∉ E₀ → ∃ C : List ℕ,
      (∀ j, j ∈ C ↔ (j < 729 ∧ T.sel j ^ 3 = 1 ∧ T.sel j * T.sel i = T.sel i * T.sel j)) ∧
      C.length ≤ 81 ∧ (C.length < 81 ∨ ∃ x ∈ C, ∃ y ∈ C, T.sel x * T.sel y ≠ T.sel y * T.sel x))
    {E : Subgroup G} (hES : E ≤ T.S) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hcube : ∀ a ∈ E, a ^ 3 = 1) (h81 : 81 ≤ Nat.card E) : E = E₀ := by
  by_contra hne
  have hnle : ¬ E ≤ E₀ := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hE₀]; exact h81))
  obtain ⟨e, heE, heE0⟩ := Set.not_subset.mp hnle
  obtain ⟨i, hi, rfl⟩ := T.exists_sel e (hES heE)
  obtain ⟨C, hCmem, hClen, hCcases⟩ := huniq i hi (hcube _ heE) heE0
  set Eidx : Finset ℕ := (Finset.range 729).filter fun j => T.sel j ∈ E with hEidx
  have hEcard : Eidx.card = Nat.card E := (T.card_eq E hES).symm
  have hsub : Eidx ⊆ C.toFinset := by
    intro j hj
    rw [hEidx, Finset.mem_filter, Finset.mem_range] at hj
    rw [List.mem_toFinset, hCmem]
    exact ⟨hj.1, hcube _ hj.2, hcomm _ hj.2 _ heE⟩
  have hCcard : C.toFinset.card ≤ C.length := List.toFinset_card_le C
  have hEC : Eidx = C.toFinset := Finset.eq_of_subset_of_card_le hsub (by omega)
  rcases hCcases with hlt | ⟨x, hx, y, hy, hxy⟩
  · have := Finset.card_le_card hsub
    omega
  · have hx' : x ∈ Eidx := by rw [hEC, List.mem_toFinset]; exact hx
    have hy' : y ∈ Eidx := by rw [hEC, List.mem_toFinset]; exact hy
    rw [hEidx, Finset.mem_filter] at hx' hy'
    exact hxy (hcomm _ hx'.2 _ hy'.2)

end Table

end CFSG.RankThree.PartOne.F106
