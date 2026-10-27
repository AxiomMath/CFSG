module

public import CFSG.Permutation.FiveTransitive.Degree25OneBelowMaximal
public import CFSG.Permutation.FiveTransitive.Degree25StabilizerMaximalTwoThree

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

private theorem three_seventh_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬3 ^ 7 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro hthreeSeventh
  have hHne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hHdiv : Nat.card H ∣ 8778792960000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_maximal_two
        X P hcard h5 hnotAlt s hs
  have hHfactorizationLe :
      (Nat.card H).factorization 3 ≤ 7 := by
    have hle :=
      (Nat.factorization_le_iff_dvd hHne
        (by norm_num : (8778792960000 : ℕ) ≠ 0)).mpr hHdiv
    have hconstant :
        (8778792960000 : ℕ).factorization 3 = 7 := by
      rw [show 8778792960000 =
          3 ^ 7 * 4014080000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 3 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simpa only [hconstant] using hle 3
  have hHfactorizationGe :
      7 ≤ (Nat.card H).factorization 3 :=
    (show Nat.Prime 3 by norm_num).pow_dvd_iff_le_factorization
      hHne |>.mp hthreeSeventh
  have hHfactorization :
      (Nat.card H).factorization 3 = 7 := by
    omega
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
  have hindexFactorization :
      (6375600 : ℕ).factorization 3 = 2 := by
    rw [show 6375600 = 3 ^ 2 * 708400 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 3 by norm_num).factorization_pow,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hPfactorization :
      (Nat.card P).factorization 3 = 9 := by
    rw [hPcard,
      Nat.factorization_mul (by norm_num) hHne,
      Finsupp.add_apply, hindexFactorization,
      hHfactorization]
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let S : Sylow 3 P := Sylow.nonempty.some
  have hScard : Nat.card S = 19683 := by
    rw [S.card_eq_multiplicity, hPfactorization]
    norm_num
  exact hnotAlt
    (alternatingGroup_le_of_sylow_three_card_nineteen_thousand
      X P hcard h5 S hScard)

private theorem two_seventeenth_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬2 ^ 17 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro htwoFifteenth
  have hHne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hHdiv : Nat.card H ∣ 8778792960000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_maximal_two
        X P hcard h5 hnotAlt s hs
  have hHfactorizationLe :
      (Nat.card H).factorization 2 ≤ 17 := by
    have hle :=
      (Nat.factorization_le_iff_dvd hHne
        (by norm_num : (8778792960000 : ℕ) ≠ 0)).mpr hHdiv
    have hconstant :
        (8778792960000 : ℕ).factorization 2 = 17 := by
      rw [show 8778792960000 =
          2 ^ 17 * 66976875 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simpa only [hconstant] using hle 2
  have hHfactorizationGe :
      17 ≤ (Nat.card H).factorization 2 :=
    (show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
      hHne |>.mp htwoFifteenth
  have hHfactorization :
      (Nat.card H).factorization 2 = 17 := by
    omega
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
  have hindexFactorization :
      (6375600 : ℕ).factorization 2 = 4 := by
    rw [show 6375600 = 2 ^ 4 * 398475 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 2 by norm_num).factorization_pow,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hPfactorization :
      (Nat.card P).factorization 2 = 21 := by
    rw [hPcard,
      Nat.factorization_mul (by norm_num) hHne,
      Finsupp.add_apply, hindexFactorization,
      hHfactorization]
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let S : Sylow 2 P := Sylow.nonempty.some
  have hScard : Nat.card S = 2097152 := by
    rw [S.card_eq_multiplicity, hPfactorization]
    norm_num
  exact hnotAlt
    (alternatingGroup_le_of_sylow_two_card_two_million
      X P hcard h5 S hScard)

private theorem five_point_stabilizer_card_dvd_without_three_seventh
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 2926264320000 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 8778792960000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_maximal_two
        X P hcard h5 hnotAlt s hs
  have hnotThreeSeventh : ¬3 ^ 7 ∣ Nat.card H := by
    simpa only [H] using
      three_seventh_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (2926264320000 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (8778792960000 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 3
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 3 < 7 := by
      rw [← not_le]
      intro hseven
      exact hnotThreeSeventh
        ((show Nat.Prime 3 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr hseven)
    have htarget :
        (2926264320000 : ℕ).factorization 3 = 6 := by
      rw [show 2926264320000 =
          3 ^ 6 * 4014080000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 3 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (8778792960000 : ℕ).factorization p =
          (2926264320000 : ℕ).factorization p := by
      have hp' : 3 ≠ p := Ne.symm hp
      rw [show 8778792960000 =
          3 * 2926264320000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 3 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

private theorem five_point_stabilizer_card_dvd_without_two_seventeenth
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 1463132160000 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 2926264320000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_three_seventh
        X P hcard h5 hnotAlt s hs
  have hnotTwoSeventeenth : ¬2 ^ 17 ∣ Nat.card H := by
    simpa only [H] using
      two_seventeenth_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (1463132160000 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (2926264320000 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 2
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 2 < 17 := by
      rw [← not_le]
      intro hfifteen
      exact hnotTwoSeventeenth
        ((show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr hfifteen)
    have htarget :
        (1463132160000 : ℕ).factorization 2 = 16 := by
      rw [show 1463132160000 =
          2 ^ 16 * 22325625 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (2926264320000 : ℕ).factorization p =
          (1463132160000 : ℕ).factorization p := by
      have hp' : 2 ≠ p := Ne.symm hp
      rw [show 2926264320000 =
          2 * 1463132160000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

private theorem two_sixteenth_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬2 ^ 16 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro htwoFourteenth
  have hHne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hHdiv : Nat.card H ∣ 1463132160000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_two_seventeenth
        X P hcard h5 hnotAlt s hs
  have hHfactorizationLe :
      (Nat.card H).factorization 2 ≤ 16 := by
    have hle :=
      (Nat.factorization_le_iff_dvd hHne
        (by norm_num : (1463132160000 : ℕ) ≠ 0)).mpr hHdiv
    have hconstant :
        (1463132160000 : ℕ).factorization 2 = 16 := by
      rw [show 1463132160000 =
          2 ^ 16 * 22325625 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simpa only [hconstant] using hle 2
  have hHfactorizationGe :
      16 ≤ (Nat.card H).factorization 2 :=
    (show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
      hHne |>.mp htwoFourteenth
  have hHfactorization :
      (Nat.card H).factorization 2 = 16 := by
    omega
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
  have hindexFactorization :
      (6375600 : ℕ).factorization 2 = 4 := by
    rw [show 6375600 = 2 ^ 4 * 398475 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 2 by norm_num).factorization_pow,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hPfactorization :
      (Nat.card P).factorization 2 = 20 := by
    rw [hPcard,
      Nat.factorization_mul (by norm_num) hHne,
      Finsupp.add_apply, hindexFactorization,
      hHfactorization]
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let S : Sylow 2 P := Sylow.nonempty.some
  have hScard : Nat.card S = 1048576 := by
    rw [S.card_eq_multiplicity, hPfactorization]
    norm_num
  exact hnotAlt
    (alternatingGroup_le_of_sylow_two_card_one_million
      X P hcard h5 S hScard)

private theorem five_point_stabilizer_card_dvd_without_two_sixteenth
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 731566080000 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 1463132160000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_two_seventeenth
        X P hcard h5 hnotAlt s hs
  have hnotTwoSixteenth : ¬2 ^ 16 ∣ Nat.card H := by
    simpa only [H] using
      two_sixteenth_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (731566080000 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (1463132160000 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 2
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 2 < 16 := by
      rw [← not_le]
      intro hfourteen
      exact hnotTwoSixteenth
        ((show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr hfourteen)
    have htarget :
        (731566080000 : ℕ).factorization 2 = 15 := by
      rw [show 731566080000 =
          2 ^ 15 * 22325625 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (1463132160000 : ℕ).factorization p =
          (731566080000 : ℕ).factorization p := by
      have hp' : 2 ≠ p := Ne.symm hp
      rw [show 1463132160000 =
          2 * 731566080000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

private theorem two_fifteenth_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬2 ^ 15 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro htwoThirteenth
  have hHne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hHdiv : Nat.card H ∣ 731566080000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_two_sixteenth
        X P hcard h5 hnotAlt s hs
  have hHfactorizationLe :
      (Nat.card H).factorization 2 ≤ 15 := by
    have hle :=
      (Nat.factorization_le_iff_dvd hHne
        (by norm_num : (731566080000 : ℕ) ≠ 0)).mpr hHdiv
    have hconstant :
        (731566080000 : ℕ).factorization 2 = 15 := by
      rw [show 731566080000 =
          2 ^ 15 * 22325625 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simpa only [hconstant] using hle 2
  have hHfactorizationGe :
      15 ≤ (Nat.card H).factorization 2 :=
    (show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
      hHne |>.mp htwoThirteenth
  have hHfactorization :
      (Nat.card H).factorization 2 = 15 := by
    omega
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
  have hindexFactorization :
      (6375600 : ℕ).factorization 2 = 4 := by
    rw [show 6375600 = 2 ^ 4 * 398475 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply,
      (show Nat.Prime 2 by norm_num).factorization_pow,
      Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hPfactorization :
      (Nat.card P).factorization 2 = 19 := by
    rw [hPcard,
      Nat.factorization_mul (by norm_num) hHne,
      Finsupp.add_apply, hindexFactorization,
      hHfactorization]
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let S : Sylow 2 P := Sylow.nonempty.some
  have hScard : Nat.card S = 524288 := by
    rw [S.card_eq_multiplicity, hPfactorization]
    norm_num
  exact hnotAlt
    (alternatingGroup_le_of_sylow_two_card_half_million
      X P hcard h5 S hScard)

theorem five_point_stabilizer_card_dvd_without_two_fifteenth
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 365783040000 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 731566080000 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_two_sixteenth
        X P hcard h5 hnotAlt s hs
  have hnotTwoFifteenth : ¬2 ^ 15 ∣ Nat.card H := by
    simpa only [H] using
      two_fifteenth_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (365783040000 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (731566080000 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 2
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 2 < 15 := by
      rw [← not_le]
      intro hthirteen
      exact hnotTwoFifteenth
        ((show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr hthirteen)
    have htarget :
        (365783040000 : ℕ).factorization 2 = 14 := by
      rw [show 365783040000 =
          2 ^ 14 * 22325625 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (731566080000 : ℕ).factorization p =
          (365783040000 : ℕ).factorization p := by
      have hp' : 2 ≠ p := Ne.symm hp
      rw [show 731566080000 =
          2 * 365783040000 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

end FiveTransitive.Degree25

end CFSG
