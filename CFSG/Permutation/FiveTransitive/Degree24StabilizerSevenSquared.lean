module

public import CFSG.Permutation.FiveTransitive.Degree24StabilizerFactorEleven
public import CFSG.Permutation.FiveTransitive.Degree24SylowSevenMax

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem seven_squared_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
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
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard :
      Nat.card P = 5100480 * Nat.card H := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hsevenCubeP : 7 ^ 3 ∣ Nat.card P := by
    change 49 ∣ Nat.card H at hsevenSq
    obtain ⟨k, hk⟩ := hsevenSq
    rw [hPcard, hk]
    refine ⟨728640 * k, ?_⟩
    norm_num [pow_succ]
    ring
  have hPdvdFactorial :
      Nat.card P ∣ (24 : ℕ).factorial := by
    have hdvd := P.card_subgroup_dvd_card
    rw [Nat.card_perm] at hdvd
    rw [Nat.card_eq_fintype_card]
    simpa only [Nat.card_eq_fintype_card, hcard] using hdvd
  have hfactorizationLe :
      (Nat.card P).factorization 7 ≤ 3 := by
    have hle :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (by norm_num : (24 : ℕ).factorial ≠ 0)).mpr
        hPdvdFactorial
    have hleSeven := hle 7
    have hfactorial :
        ((24 : ℕ).factorial).factorization 7 = 3 := by
      rw [show (24 : ℕ).factorial =
          7 * (7 * (7 * 1808887468610027520000)) by norm_num,
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

theorem five_point_stabilizer_card_dvd_without_seven_squared
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 376233984000 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 2633637888000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_eleven
        X P hcard h5 hnotAlt s hs
  have hnotSevenSq : ¬7 ^ 2 ∣ Nat.card H := by
    simpa only [H] using
      seven_squared_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (376233984000 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (2633637888000 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 7
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 7 < 2 := by
      rw [← not_le]
      intro htwo
      exact hnotSevenSq
        ((show Nat.Prime 7 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr htwo)
    have htarget :
        (376233984000 : ℕ).factorization 7 = 1 := by
      rw [show 376233984000 = 7 * 53747712000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 7 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (2633637888000 : ℕ).factorization p =
          (376233984000 : ℕ).factorization p := by
      have hp' : 7 ≠ p := Ne.symm hp
      rw [show 2633637888000 =
          7 * 376233984000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 7 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

end FiveTransitive.Degree24

end CFSG
