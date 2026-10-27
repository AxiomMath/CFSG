module

public import CFSG.Permutation.FiveTransitive.Degree25SylowSevenMax

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

theorem seven_squared_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬7 ^ 2 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro hsevenSq
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 6375600 := by
    change (fixingSubgroup P s).index = 6375600
    omega
  have hHindexCard := H.index_mul_card
  have hPcard :
      Nat.card P = 6375600 * Nat.card H := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hsevenCubeP : 7 ^ 3 ∣ Nat.card P := by
    change 49 ∣ Nat.card H at hsevenSq
    obtain ⟨k, hk⟩ := hsevenSq
    rw [hPcard, hk]
    refine ⟨910800 * k, ?_⟩
    norm_num [pow_succ]
    ring
  have hPdvdFactorial :
      Nat.card P ∣ (25 : ℕ).factorial := by
    have hdvd := P.card_subgroup_dvd_card
    rw [Nat.card_perm] at hdvd
    rw [Nat.card_eq_fintype_card]
    simpa only [Nat.card_eq_fintype_card, hcard] using hdvd
  have hfactorizationLe :
      (Nat.card P).factorization 7 ≤ 3 := by
    have hle :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (by norm_num : (25 : ℕ).factorial ≠ 0)).mpr
        hPdvdFactorial
    have hleSeven := hle 7
    have hfactorial :
        ((25 : ℕ).factorial).factorization 7 = 3 := by
      have hfactorial24 :
          ((24 : ℕ).factorial).factorization 7 = 3 := by
        rw [show (24 : ℕ).factorial =
            7 * (7 * (7 * 1808887468610027520000)) by
              norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply,
          (show Nat.Prime 7 by norm_num).factorization,
          Finsupp.single_eq_same,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply,
          (show Nat.Prime 7 by norm_num).factorization,
          Finsupp.single_eq_same,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply,
          (show Nat.Prime 7 by norm_num).factorization,
          Finsupp.single_eq_same,
          Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
        norm_num
      rw [show (25 : ℕ).factorial =
          25 * (24 : ℕ).factorial by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num),
        hfactorial24]
    rw [hfactorial] at hleSeven
    exact hleSeven
  have hfactorizationGe :
      3 ≤ (Nat.card P).factorization 7 :=
    (show Nat.Prime 7 by norm_num).pow_dvd_iff_le_factorization
      Nat.card_pos.ne' |>.mp hsevenCubeP
  have hfactorization :
      (Nat.card P).factorization 7 = 3 := by
    omega
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let S : Sylow 7 P := Sylow.nonempty.some
  have hScard : Nat.card S = 343 := by
    rw [S.card_eq_multiplicity, hfactorization]
    norm_num
  exact
    sylow_seven_card_ne_three_hundred_forty_three
      X P hcard h5 hnotAlt S hScard

end FiveTransitive.Degree25

end CFSG
