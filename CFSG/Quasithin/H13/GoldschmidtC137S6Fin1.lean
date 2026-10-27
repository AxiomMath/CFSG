module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.Background.B3Tab

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin.B3

@[expose] def T6l : List Tab :=
  [[0,1,2,3,4,5], [0,1,2,3,5,4], [0,1,3,2,4,5], [0,1,3,2,5,4], [1,0,2,3,4,5], [1,0,2,3,5,4],
    [1,0,3,2,4,5], [1,0,3,2,5,4], [2,3,0,1,4,5], [2,3,0,1,5,4], [2,3,1,0,4,5], [2,3,1,0,5,4],
    [3,2,0,1,4,5], [3,2,0,1,5,4], [3,2,1,0,4,5], [3,2,1,0,5,4]]

@[expose] def H1l : List Tab :=
  [[0,1,2,3,4,5], [0,1,2,3,5,4], [0,1,3,2,4,5], [0,1,3,2,5,4], [0,2,1,3,4,5], [0,2,1,3,5,4],
    [0,2,3,1,4,5], [0,2,3,1,5,4], [0,3,1,2,4,5], [0,3,1,2,5,4], [0,3,2,1,4,5], [0,3,2,1,5,4],
    [1,0,2,3,4,5], [1,0,2,3,5,4], [1,0,3,2,4,5], [1,0,3,2,5,4], [1,2,0,3,4,5], [1,2,0,3,5,4],
    [1,2,3,0,4,5], [1,2,3,0,5,4], [1,3,0,2,4,5], [1,3,0,2,5,4], [1,3,2,0,4,5], [1,3,2,0,5,4],
    [2,0,1,3,4,5], [2,0,1,3,5,4], [2,0,3,1,4,5], [2,0,3,1,5,4], [2,1,0,3,4,5], [2,1,0,3,5,4],
    [2,1,3,0,4,5], [2,1,3,0,5,4], [2,3,0,1,4,5], [2,3,0,1,5,4], [2,3,1,0,4,5], [2,3,1,0,5,4],
    [3,0,1,2,4,5], [3,0,1,2,5,4], [3,0,2,1,4,5], [3,0,2,1,5,4], [3,1,0,2,4,5], [3,1,0,2,5,4],
    [3,1,2,0,4,5], [3,1,2,0,5,4], [3,2,0,1,4,5], [3,2,0,1,5,4], [3,2,1,0,4,5], [3,2,1,0,5,4]]

@[expose] def H2l : List Tab :=
  [[0,1,2,3,4,5], [0,1,2,3,5,4], [0,1,3,2,4,5], [0,1,3,2,5,4], [0,1,4,5,2,3], [0,1,4,5,3,2],
    [0,1,5,4,2,3], [0,1,5,4,3,2], [1,0,2,3,4,5], [1,0,2,3,5,4], [1,0,3,2,4,5], [1,0,3,2,5,4],
    [1,0,4,5,2,3], [1,0,4,5,3,2], [1,0,5,4,2,3], [1,0,5,4,3,2], [2,3,0,1,4,5], [2,3,0,1,5,4],
    [2,3,1,0,4,5], [2,3,1,0,5,4], [2,3,4,5,0,1], [2,3,4,5,1,0], [2,3,5,4,0,1], [2,3,5,4,1,0],
    [3,2,0,1,4,5], [3,2,0,1,5,4], [3,2,1,0,4,5], [3,2,1,0,5,4], [3,2,4,5,0,1], [3,2,4,5,1,0],
    [3,2,5,4,0,1], [3,2,5,4,1,0], [4,5,0,1,2,3], [4,5,0,1,3,2], [4,5,1,0,2,3], [4,5,1,0,3,2],
    [4,5,2,3,0,1], [4,5,2,3,1,0], [4,5,3,2,0,1], [4,5,3,2,1,0], [5,4,0,1,2,3], [5,4,0,1,3,2],
    [5,4,1,0,2,3], [5,4,1,0,3,2], [5,4,2,3,0,1], [5,4,2,3,1,0], [5,4,3,2,0,1], [5,4,3,2,1,0]]

@[expose] def R1l : List Tab :=
  [[0,1,2,3,4,5], [0,1,2,3,5,4], [1,0,3,2,4,5], [1,0,3,2,5,4], [2,3,0,1,4,5], [2,3,0,1,5,4],
    [3,2,1,0,4,5], [3,2,1,0,5,4]]

@[expose] def R2l : List Tab :=
  [[0,1,2,3,4,5], [0,1,2,3,5,4], [0,1,3,2,4,5], [0,1,3,2,5,4], [1,0,2,3,4,5], [1,0,2,3,5,4],
    [1,0,3,2,4,5], [1,0,3,2,5,4]]

set_option maxRecDepth 100000 in
theorem subOK_lists : subOK 6 T6l = true ∧ subOK 6 H1l = true ∧ subOK 6 H2l = true ∧
    subOK 6 R1l = true ∧ subOK 6 R2l = true := by decide +kernel

noncomputable abbrev T6 : Subgroup (Gp 6) := subOf 6 T6l
noncomputable abbrev H1 : Subgroup (Gp 6) := subOf 6 H1l
noncomputable abbrev H2 : Subgroup (Gp 6) := subOf 6 H2l
noncomputable abbrev R1 : Subgroup (Gp 6) := subOf 6 R1l
noncomputable abbrev R2 : Subgroup (Gp 6) := subOf 6 R2l

theorem mem_T6 {σ : Gp 6} : σ ∈ T6 ↔ tab σ ∈ T6l := mem_subOf subOK_lists.1
theorem mem_H1 {σ : Gp 6} : σ ∈ H1 ↔ tab σ ∈ H1l := mem_subOf subOK_lists.2.1
theorem mem_H2 {σ : Gp 6} : σ ∈ H2 ↔ tab σ ∈ H2l := mem_subOf subOK_lists.2.2.1
theorem mem_R1 {σ : Gp 6} : σ ∈ R1 ↔ tab σ ∈ R1l := mem_subOf subOK_lists.2.2.2.1
theorem mem_R2 {σ : Gp 6} : σ ∈ R2 ↔ tab σ ∈ R2l := mem_subOf subOK_lists.2.2.2.2

theorem card_T6 : Nat.card T6 = 16 := by
  rw [card_subOf subOK_lists.1]; decide +kernel
theorem card_H1 : Nat.card H1 = 48 := by
  rw [card_subOf subOK_lists.2.1]; decide +kernel
theorem card_H2 : Nat.card H2 = 48 := by
  rw [card_subOf subOK_lists.2.2.1]; decide +kernel
set_option maxRecDepth 100000 in
theorem sub_lists :
    (∀ t ∈ T6l, t ∈ H1l ∧ t ∈ H2l) ∧ (∀ t ∈ H1l, t ∈ H2l → t ∈ T6l) ∧
      (∀ t ∈ R1l, t ∈ T6l) ∧ (∀ t ∈ R2l, t ∈ T6l) := by decide +kernel

theorem T6_le_H1 : T6 ≤ H1 := fun σ hσ => by
  rw [mem_T6] at hσ
  rw [mem_H1]
  exact (sub_lists.1 _ hσ).1

theorem T6_le_H2 : T6 ≤ H2 := fun σ hσ => by
  rw [mem_T6] at hσ
  rw [mem_H2]
  exact (sub_lists.1 _ hσ).2

theorem H1_inf_H2 : H1 ⊓ H2 = T6 := by
  apply le_antisymm
  · rintro σ ⟨h1, h2⟩
    have h1' : σ ∈ H1 := h1
    have h2' : σ ∈ H2 := h2
    rw [mem_H1] at h1'
    rw [mem_H2] at h2'
    exact (mem_T6).2 (sub_lists.2.1 _ h1' h2')
  · exact le_inf T6_le_H1 T6_le_H2

theorem R1_le_T6 : R1 ≤ T6 := fun σ hσ => by
  rw [mem_R1] at hσ
  rw [mem_T6]
  exact sub_lists.2.2.1 _ hσ

theorem R2_le_T6 : R2 ≤ T6 := fun σ hσ => by
  rw [mem_R2] at hσ
  rw [mem_T6]
  exact sub_lists.2.2.2 _ hσ

end CFSG.Quasithin.H13.U3.GC137
