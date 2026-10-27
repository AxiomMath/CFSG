module

public import CFSG.RankThree.PartOne.Q1327C.BTransfer
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.Q1327.Defs

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne

variable {G : Type} [Group G]

@[expose] def M3Cell (p : ℕ) (X : Subgroup G) : Prop :=
  (∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 4 2 f) ∨
    (∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSp 3 2 f) ∨
    (∃ f : ℕ, 1 ≤ f ∧ (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) ∧
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .POmegaMinus 4 2 f) ∨
    (∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ (p ≠ 5 ∨ 25 ∣ 2 ^ f + 1) ∧
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 5 2 f)

@[expose] def BOutcome (p : ℕ) (X : Subgroup G) : Prop :=
  RowModel p X 9 ∨ RowModel p X 10 ∨ RowModel p X 12 ∨ M3Cell p X

namespace BOutcome

variable {p : ℕ} {X : Subgroup G}

theorem of_row9 (h : RowModel p X 9) : BOutcome p X := Or.inl h

theorem of_row10 (h : RowModel p X 10) : BOutcome p X := Or.inr (Or.inl h)

theorem of_row12 (h : RowModel p X 12) : BOutcome p X := Or.inr (Or.inr (Or.inl h))

theorem of_L4 (h : ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
    StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSL 4 2 f) : BOutcome p X :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem of_Sp6 (h : ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
    StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSp 3 2 f) : BOutcome p X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem of_Om8 (h : ∃ f : ℕ, 1 ≤ f ∧ (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) ∧
    StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .POmegaMinus 4 2 f) : BOutcome p X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem of_U5 (h : ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧ (p ≠ 5 ∨ 25 ∣ 2 ^ f + 1) ∧
    StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 5 2 f) : BOutcome p X :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

end BOutcome

theorem false_of_row_rank_two [Finite G] {p : ℕ} {X A₀ F : Subgroup G}
    (h : Q1327.T123Base p X A₀ F) {r : ℕ} (hr : RowRank r = 2) (hd : RowData p X F r) : False := by
  have h1 := hd.2.1
  rw [hr, h.F_card] at h1
  have h5 := h.five_le
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

section Bar

variable [Finite G] {p : ℕ} {X A₀ F : Subgroup G}

theorem barF_elem (h : Q1327.T123Base p X A₀ F) : IsElementaryAbelian p (bar X F) :=
  bar_isElementaryAbelian h.prime h.F_le h.F_elem

theorem barF_card (h : Q1327.T123Base p X A₀ F) : Nat.card (bar X F) = p ^ 3 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.F_elem
  rw [bar_card h.prime h.center_pPrime h.F_le (IsElementaryAbelian.isPGroup p F), h.F_card]

theorem barF_exp (h : Q1327.T123Base p X A₀ F) : ∀ x ∈ bar X F, x ^ p = 1 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := barF_elem h
  intro x hx
  exact elemPow_eq_one_of_isElementaryAbelian (A := bar X F) x hx

theorem barF_isPGroup (h : Q1327.T123Base p X A₀ F) : IsPGroup p F := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.F_elem
  exact IsElementaryAbelian.isPGroup p F

@[expose] noncomputable def barF_equiv (h : Q1327.T123Base p X A₀ F) : F ≃* bar X F :=
  barEquiv h.prime h.center_pPrime h.F_le (barF_isPGroup h)

theorem torusWeyl_bar_le_B (h : Q1327.T123Base p X A₀ F) :
    torusWeyl (bar X F) ≤ (torusImage F X).map (MulAut.congr (barF_equiv h)).toMonoidHom :=
  torusWeyl_bar_le h.prime h.center_pPrime h.F_le h.F_elem

theorem pow_three_dvd_card_X (h : Q1327.T123Base p X A₀ F) : p ^ 3 ∣ Nat.card ↥X := by
  have h1 : Nat.card (F.subgroupOf X) = p ^ 3 := by
    rw [← h.F_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.F_le).toEquiv
  rw [← h1]
  exact Subgroup.card_subgroup_dvd_card _

theorem pow_three_dvd_card_quot (h : Q1327.T123Base p X A₀ F) :
    p ^ 3 ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) := by
  rw [← barF_card h]
  exact Subgroup.card_subgroup_dvd_card _

end Bar

end CFSG.RankThree.PartOne.Q1327C
