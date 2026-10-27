module

public import CFSG.Permutation.FiveTransitive.Degree25StabilizerOneBelow
public import CFSG.Permutation.FiveTransitive.Degree25StabilizerSevenSquared

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

private theorem five_fourth_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬5 ^ 4 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro hfifthFourth
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
  have hfifthSixthP : 5 ^ 6 ∣ Nat.card P := by
    change 625 ∣ Nat.card H at hfifthFourth
    obtain ⟨k, hk⟩ := hfifthFourth
    rw [hPcard, hk]
    refine ⟨255024 * k, ?_⟩
    norm_num [pow_succ]
    ring
  have hPdvdFactorial :
      Nat.card P ∣ (25 : ℕ).factorial := by
    have hdvd := P.card_subgroup_dvd_card
    rw [Nat.card_perm] at hdvd
    rw [Nat.card_eq_fintype_card]
    simpa only [Nat.card_eq_fintype_card, hcard] using hdvd
  have hfactorial :
      ((25 : ℕ).factorial).factorization 5 = 6 := by
    rw [show (25 : ℕ).factorial =
        5 ^ 6 * 992717442773183102976 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 5 by norm_num).factorization_pow,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hfactorizationLe :
      (Nat.card P).factorization 5 ≤ 6 := by
    have hle :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (by norm_num : (25 : ℕ).factorial ≠ 0)).mpr
        hPdvdFactorial
    simpa only [hfactorial] using hle 5
  have hfactorizationGe :
      6 ≤ (Nat.card P).factorization 5 :=
    (show Nat.Prime 5 by norm_num).pow_dvd_iff_le_factorization
      Nat.card_pos.ne' |>.mp hfifthSixthP
  have hfactorization :
      (Nat.card P).factorization 5 = 6 := by
    omega
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let S : Sylow 5 P := Sylow.nonempty.some
  have hScard :
      Nat.card S =
        5 ^ (Nat.card (Equiv.Perm X)).factorization 5 := by
    rw [S.card_eq_multiplicity, hfactorization,
      Nat.card_perm, Nat.card_eq_fintype_card,
      hcard, hfactorial]
  exact hnotAlt
    (alternatingGroup_le_of_maximal_sylow_five
      X P hcard h5 S hScard)

private theorem five_point_stabilizer_card_dvd_without_five_fourth
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 73156608000 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 365783040000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_two_fifteenth
        X P hcard h5 hnotAlt s hs
  have hnotFiveFourth : ¬5 ^ 4 ∣ Nat.card H := by
    simpa only [H] using
      five_fourth_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (73156608000 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (365783040000 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 5
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 5 < 4 := by
      rw [← not_le]
      intro hfour
      exact hnotFiveFourth
        ((show Nat.Prime 5 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr hfour)
    have htarget :
        (73156608000 : ℕ).factorization 5 = 3 := by
      rw [show 73156608000 =
          5 ^ 3 * 585252864 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 5 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (365783040000 : ℕ).factorization p =
          (73156608000 : ℕ).factorization p := by
      have hp' : 5 ≠ p := Ne.symm hp
      rw [show 365783040000 =
          5 * 73156608000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 5 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

theorem five_point_stabilizer_card_dvd_final
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 10450944000 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 73156608000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_five_fourth
        X P hcard h5 hnotAlt s hs
  have hnotSevenSquared : ¬7 ^ 2 ∣ Nat.card H := by
    simpa only [H] using
      seven_squared_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (10450944000 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (73156608000 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 7
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 7 < 2 := by
      rw [← not_le]
      intro htwo
      exact hnotSevenSquared
        ((show Nat.Prime 7 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr htwo)
    have htarget :
        (10450944000 : ℕ).factorization 7 = 1 := by
      rw [show 10450944000 =
          7 * 1492992000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 7 by norm_num).factorization,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (73156608000 : ℕ).factorization p =
          (10450944000 : ℕ).factorization p := by
      have hp' : 7 ≠ p := Ne.symm hp
      rw [show 73156608000 =
          7 * 10450944000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 7 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

end FiveTransitive.Degree25

end CFSG
