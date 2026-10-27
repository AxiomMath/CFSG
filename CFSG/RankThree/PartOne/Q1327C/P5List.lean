module

public import CFSG.RankThree.PartOne.Q1327.Defs
public import CFSG.RankThree.PartOne.Q1327C.P5Simple
public import CFSG.RankThree.PartOne.Q1327C.P5Glue

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N143
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

theorem kf1327P5List_holds :
    ∀ (G : Type) [Group G] [Finite G] (X A₀ F : Subgroup G),
      Q1327.T123Base 5 X A₀ F → Census3.TheoremThreeList (↥X ⧸ Subgroup.center ↥X) →
      (∃ (a : G) (N : Subgroup G) (f : ℕ), a ∈ F ∧ a ≠ 1 ∧
        N ≤ X ⊓ Subgroup.centralizer ({a} : Set G) ∧ 2 ≤ f ∧ 5 ∣ 2 ^ f + 1 ∧
        StatedClassicalModel (↥N ⧸ aschbacherSolvableCore 5 ↥N) .PSU 3 2 f) →
      ListEvenItem (↥X ⧸ Subgroup.center ↥X) := by
  intro G _ _ X A₀ F hb hlist hN
  obtain ⟨a, N, f, -, -, hNle, hf2, h5f, hmod⟩ := hN
  have : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) := hb.quasisimple.2.1
  have h13 := thirteen_dvd_of_section (hNle.trans inf_le_left) hf2 h5f hmod
  have hFX : 5 ^ 3 ∣ Nat.card ↥X := hb.F_card ▸ Subgroup.card_dvd_of_le hb.F_le
  have hcop : Nat.Coprime (5 ^ 3) (Nat.card (Subgroup.center ↥X)) :=
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hb.center_pPrime)
  have hmul : Nat.card ↥X =
      Nat.card (Subgroup.center ↥X) * Nat.card (↥X ⧸ Subgroup.center ↥X) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥X), mul_comm]
  have h5 : 5 ^ 3 ∣ Nat.card (↥X ⧸ Subgroup.center ↥X) :=
    hcop.dvd_of_dvd_mul_left (hmul ▸ hFX)
  obtain ⟨S, hSX, hS1, hS2, hAN, hSA⟩ := hb.A₀_invariant
  obtain ⟨B, T, hB, hBcard, hT2, hT1, hBN, hBT⟩ :=
    section_of_center hb.center_pPrime hb.A₀_le hSX hb.A₀_elem hS2 hS1 hAN hSA.symm
  have := hB
  exact p5_simple hlist h5 h13 (E := B) (S := T) (hBcard.trans hb.A₀_card).symm.le hT1 hT2
    hBN hBT

end CFSG.RankThree.PartOne.Q1327C
