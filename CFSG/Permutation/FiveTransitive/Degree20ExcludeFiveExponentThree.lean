module

public import CFSG.Permutation.FiveTransitive.Degree20SylowFiveMax

public section

namespace CFSG

namespace FiveTransitive.Degree20

open MulAction SubMulAction Subgroup

private theorem factorization_five_mul
    (n : ℕ) (hn : n ≠ 0) :
    (5 * n).factorization 5 =
      1 + n.factorization 5 := by
  rw [Nat.factorization_mul (by norm_num) hn,
    Finsupp.add_apply,
    (show Nat.Prime 5 by norm_num).factorization,
    Finsupp.single_eq_same]

theorem factorization_five_cube_mul_of_not_dvd
    (n : ℕ) (hn : n ≠ 0) (hnot : ¬5 ∣ n) :
    (5 * (5 * (5 * n))).factorization 5 = 3 := by
  rw [factorization_five_mul _ (by positivity),
    factorization_five_mul _ (by positivity),
    factorization_five_mul n hn,
    Nat.factorization_eq_zero_of_not_dvd hnot]

theorem five_point_stabilizer_card_not_five_exponent_three
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ≠ 144000 ∧
      Nat.card (fixingSubgroup P s) ≠ 46656000 := by
  classical
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hindex :
      (fixingSubgroup P s).index = 1860480 := by
    omega
  have hindexCard :=
    (fixingSubgroup P s).index_mul_card
  have hPcard :
      Nat.card P =
        1860480 * Nat.card (fixingSubgroup P s) := by
    rw [hindex] at hindexCard
    exact hindexCard.symm
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let S : Sylow 5 P := Sylow.nonempty.some
  have hfactorizationOrbit :
      (1860480 : ℕ).factorization 5 = 1 := by
    rw [show 1860480 = 5 * 372096 by norm_num,
      factorization_five_mul 372096 (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hfactorizationFirst :
      (144000 : ℕ).factorization 5 = 3 := by
    rw [show 144000 = 5 * (5 * (5 * 1152)) by norm_num]
    exact factorization_five_cube_mul_of_not_dvd
      1152 (by norm_num) (by norm_num)
  have hfactorizationSecond :
      (46656000 : ℕ).factorization 5 = 3 := by
    rw [show 46656000 = 5 * (5 * (5 * 373248)) by norm_num]
    exact factorization_five_cube_mul_of_not_dvd
      373248 (by norm_num) (by norm_num)
  have forceAlternating
      (hHcard :
        Nat.card (fixingSubgroup P s) = 144000 ∨
          Nat.card (fixingSubgroup P s) = 46656000) :
      alternatingGroup X ≤ P := by
    have hScard : Nat.card S = 625 := by
      rcases hHcard with hHcard | hHcard
      · rw [S.card_eq_multiplicity, hPcard, hHcard,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply, hfactorizationOrbit,
          hfactorizationFirst]
        norm_num
      · rw [S.card_eq_multiplicity, hPcard, hHcard,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply, hfactorizationOrbit,
          hfactorizationSecond]
        norm_num
    exact
      alternatingGroup_le_of_sylow_five_card_eq_six_hundred_twenty_five
        X P hcard h5 S hScard
  constructor
  · intro hHcard
    exact hnotAlt (forceAlternating (Or.inl hHcard))
  · intro hHcard
    exact hnotAlt (forceAlternating (Or.inr hHcard))

end FiveTransitive.Degree20

end CFSG
