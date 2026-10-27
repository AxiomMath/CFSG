module

public import CFSG.Permutation.FiveTransitive.Degree25MaximalSylowSmallSupport
public import CFSG.Permutation.FiveTransitive.Degree25StabilizerFactor

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

private theorem three_eighth_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬3 ^ 8 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro hthreeEighth
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
  have hthreeTenthP : 3 ^ 10 ∣ Nat.card P := by
    change 6561 ∣ Nat.card H at hthreeEighth
    obtain ⟨k, hk⟩ := hthreeEighth
    rw [hPcard, hk]
    refine ⟨708400 * k, ?_⟩
    norm_num [pow_succ]
    ring
  have hPdvdFactorial :
      Nat.card P ∣ (25 : ℕ).factorial := by
    have hdvd := P.card_subgroup_dvd_card
    rw [Nat.card_perm] at hdvd
    rw [Nat.card_eq_fintype_card]
    simpa only [Nat.card_eq_fintype_card, hcard] using hdvd
  have hfactorial :
      ((25 : ℕ).factorial).factorization 3 = 10 := by
    rw [show (25 : ℕ).factorial =
        3 ^ 10 * 262683704098816000000 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 3 by norm_num).factorization_pow,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hfactorizationLe :
      (Nat.card P).factorization 3 ≤ 10 := by
    have hle :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (by norm_num : (25 : ℕ).factorial ≠ 0)).mpr
        hPdvdFactorial
    simpa only [hfactorial] using hle 3
  have hfactorizationGe :
      10 ≤ (Nat.card P).factorization 3 :=
    (show Nat.Prime 3 by norm_num).pow_dvd_iff_le_factorization
      Nat.card_pos.ne' |>.mp hthreeTenthP
  have hfactorization :
      (Nat.card P).factorization 3 = 10 := by
    omega
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let S : Sylow 3 P := Sylow.nonempty.some
  have hScard :
      Nat.card S =
        3 ^ (Nat.card (Equiv.Perm X)).factorization 3 := by
    rw [S.card_eq_multiplicity, hfactorization,
      Nat.card_perm, Nat.card_eq_fintype_card,
      hcard, hfactorial]
  exact hnotAlt
    (alternatingGroup_le_of_maximal_sylow_three
      X P hcard h5 S hScard)

private theorem two_eighteenth_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬2 ^ 18 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro htwoEighteenth
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
  have htwoTwentySecondP : 2 ^ 22 ∣ Nat.card P := by
    change 262144 ∣ Nat.card H at htwoEighteenth
    obtain ⟨k, hk⟩ := htwoEighteenth
    rw [hPcard, hk]
    refine ⟨398475 * k, ?_⟩
    norm_num [pow_succ]
    ring
  have hPdvdFactorial :
      Nat.card P ∣ (25 : ℕ).factorial := by
    have hdvd := P.card_subgroup_dvd_card
    rw [Nat.card_perm] at hdvd
    rw [Nat.card_eq_fintype_card]
    simpa only [Nat.card_eq_fintype_card, hcard] using hdvd
  have hfactorial :
      ((25 : ℕ).factorial).factorization 2 = 22 := by
    rw [show (25 : ℕ).factorial =
        2 ^ 22 * 3698160658676859375 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 2 by norm_num).factorization_pow,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hfactorizationLe :
      (Nat.card P).factorization 2 ≤ 22 := by
    have hle :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (by norm_num : (25 : ℕ).factorial ≠ 0)).mpr
        hPdvdFactorial
    simpa only [hfactorial] using hle 2
  have hfactorizationGe :
      22 ≤ (Nat.card P).factorization 2 :=
    (show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
      Nat.card_pos.ne' |>.mp htwoTwentySecondP
  have hfactorization :
      (Nat.card P).factorization 2 = 22 := by
    omega
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let S : Sylow 2 P := Sylow.nonempty.some
  have hScard :
      Nat.card S =
        2 ^ (Nat.card (Equiv.Perm X)).factorization 2 := by
    rw [S.card_eq_multiplicity, hfactorization,
      Nat.card_perm, Nat.card_eq_fintype_card,
      hcard, hfactorial]
  exact hnotAlt
    (alternatingGroup_le_of_maximal_sylow_two
      X P hcard h5 S hScard)

private theorem five_point_stabilizer_card_dvd_without_three_eighth
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 17557585920000 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 52672757760000 := by
    have hdivRaw :=
      five_point_stabilizer_card_dvd_reduced
        X P hcard h5 hnotAlt s hs
    norm_num at hdivRaw
    simpa only [H] using hdivRaw
  have hnotThreeEighth : ¬3 ^ 8 ∣ Nat.card H := by
    simpa only [H] using
      three_eighth_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (17557585920000 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (52672757760000 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 3
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 3 < 8 := by
      rw [← not_le]
      intro height
      exact hnotThreeEighth
        ((show Nat.Prime 3 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr height)
    have htarget :
        (17557585920000 : ℕ).factorization 3 = 7 := by
      rw [show 17557585920000 =
          3 ^ 7 * 8028160000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 3 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (52672757760000 : ℕ).factorization p =
          (17557585920000 : ℕ).factorization p := by
      have hp' : 3 ≠ p := Ne.symm hp
      rw [show 52672757760000 =
          3 * 17557585920000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 3 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

theorem five_point_stabilizer_card_dvd_without_maximal_two
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 8778792960000 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 17557585920000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_three_eighth
        X P hcard h5 hnotAlt s hs
  have hnotTwoEighteenth : ¬2 ^ 18 ∣ Nat.card H := by
    simpa only [H] using
      two_eighteenth_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (8778792960000 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (17557585920000 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 2
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 2 < 18 := by
      rw [← not_le]
      intro height
      exact hnotTwoEighteenth
        ((show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr height)
    have htarget :
        (8778792960000 : ℕ).factorization 2 = 17 := by
      rw [show 8778792960000 =
          2 ^ 17 * 66976875 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (17557585920000 : ℕ).factorization p =
          (8778792960000 : ℕ).factorization p := by
      have hp' : 2 ≠ p := Ne.symm hp
      rw [show 17557585920000 =
          2 * 8778792960000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

end FiveTransitive.Degree25

end CFSG
