module

public import CFSG.Permutation.FiveTransitive.Degree24OneBelowMaximal
public import CFSG.Permutation.FiveTransitive.Degree24StabilizerMaximalTwoThree

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem three_seventh_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
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
  have hHdiv : Nat.card H ∣ 12541132800 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_maximal_two
        X P hcard h5 hnotAlt s hs
  have hHfactorizationLe :
      (Nat.card H).factorization 3 ≤ 7 := by
    have hle :=
      (Nat.factorization_le_iff_dvd hHne
        (by norm_num : (12541132800 : ℕ) ≠ 0)).mpr hHdiv
    have hconstant :
        (12541132800 : ℕ).factorization 3 = 7 := by
      rw [show 12541132800 =
          3 ^ 7 * 5734400 by norm_num,
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
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard :
      Nat.card P = 5100480 * Nat.card H := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hindexFactorization :
      (5100480 : ℕ).factorization 3 = 2 := by
    rw [show 5100480 = 3 ^ 2 * 566720 by norm_num,
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

private theorem two_fifteenth_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬2 ^ 15 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro htwoFifteenth
  have hHne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hHdiv : Nat.card H ∣ 12541132800 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_maximal_two
        X P hcard h5 hnotAlt s hs
  have hHfactorizationLe :
      (Nat.card H).factorization 2 ≤ 15 := by
    have hle :=
      (Nat.factorization_le_iff_dvd hHne
        (by norm_num : (12541132800 : ℕ) ≠ 0)).mpr hHdiv
    have hconstant :
        (12541132800 : ℕ).factorization 2 = 15 := by
      rw [show 12541132800 =
          2 ^ 15 * 382725 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simpa only [hconstant] using hle 2
  have hHfactorizationGe :
      15 ≤ (Nat.card H).factorization 2 :=
    (show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
      hHne |>.mp htwoFifteenth
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
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard :
      Nat.card P = 5100480 * Nat.card H := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hindexFactorization :
      (5100480 : ℕ).factorization 2 = 6 := by
    rw [show 5100480 = 2 ^ 6 * 79695 by norm_num,
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
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 4180377600 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 12541132800 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_maximal_two
        X P hcard h5 hnotAlt s hs
  have hnotThreeSeventh : ¬3 ^ 7 ∣ Nat.card H := by
    simpa only [H] using
      three_seventh_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (4180377600 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (12541132800 : ℕ) ≠ 0)).mpr hdiv) p
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
        (4180377600 : ℕ).factorization 3 = 6 := by
      rw [show 4180377600 =
          3 ^ 6 * 5734400 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 3 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (12541132800 : ℕ).factorization p =
          (4180377600 : ℕ).factorization p := by
      have hp' : 3 ≠ p := Ne.symm hp
      rw [show 12541132800 =
          3 * 4180377600 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 3 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

private theorem five_point_stabilizer_card_dvd_without_two_fifteenth
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 2090188800 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 4180377600 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_three_seventh
        X P hcard h5 hnotAlt s hs
  have hnotTwoFifteenth : ¬2 ^ 15 ∣ Nat.card H := by
    simpa only [H] using
      two_fifteenth_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (2090188800 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (4180377600 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 2
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 2 < 15 := by
      rw [← not_le]
      intro hfifteen
      exact hnotTwoFifteenth
        ((show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr hfifteen)
    have htarget :
        (2090188800 : ℕ).factorization 2 = 14 := by
      rw [show 2090188800 =
          2 ^ 14 * 127575 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (4180377600 : ℕ).factorization p =
          (2090188800 : ℕ).factorization p := by
      have hp' : 2 ≠ p := Ne.symm hp
      rw [show 4180377600 =
          2 * 2090188800 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

private theorem two_fourteenth_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬2 ^ 14 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro htwoFourteenth
  have hHne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hHdiv : Nat.card H ∣ 2090188800 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_two_fifteenth
        X P hcard h5 hnotAlt s hs
  have hHfactorizationLe :
      (Nat.card H).factorization 2 ≤ 14 := by
    have hle :=
      (Nat.factorization_le_iff_dvd hHne
        (by norm_num : (2090188800 : ℕ) ≠ 0)).mpr hHdiv
    have hconstant :
        (2090188800 : ℕ).factorization 2 = 14 := by
      rw [show 2090188800 =
          2 ^ 14 * 127575 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simpa only [hconstant] using hle 2
  have hHfactorizationGe :
      14 ≤ (Nat.card H).factorization 2 :=
    (show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
      hHne |>.mp htwoFourteenth
  have hHfactorization :
      (Nat.card H).factorization 2 = 14 := by
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
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard :
      Nat.card P = 5100480 * Nat.card H := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hindexFactorization :
      (5100480 : ℕ).factorization 2 = 6 := by
    rw [show 5100480 = 2 ^ 6 * 79695 by norm_num,
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

private theorem five_point_stabilizer_card_dvd_without_two_fourteenth
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 1045094400 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 2090188800 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_two_fifteenth
        X P hcard h5 hnotAlt s hs
  have hnotTwoFourteenth : ¬2 ^ 14 ∣ Nat.card H := by
    simpa only [H] using
      two_fourteenth_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (1045094400 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (2090188800 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 2
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 2 < 14 := by
      rw [← not_le]
      intro hfourteen
      exact hnotTwoFourteenth
        ((show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr hfourteen)
    have htarget :
        (1045094400 : ℕ).factorization 2 = 13 := by
      rw [show 1045094400 =
          2 ^ 13 * 127575 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (2090188800 : ℕ).factorization p =
          (1045094400 : ℕ).factorization p := by
      have hp' : 2 ≠ p := Ne.symm hp
      rw [show 2090188800 =
          2 * 1045094400 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

private theorem two_thirteenth_not_dvd_five_point_stabilizer_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬2 ^ 13 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  intro htwoThirteenth
  have hHne : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have hHdiv : Nat.card H ∣ 1045094400 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_two_fourteenth
        X P hcard h5 hnotAlt s hs
  have hHfactorizationLe :
      (Nat.card H).factorization 2 ≤ 13 := by
    have hle :=
      (Nat.factorization_le_iff_dvd hHne
        (by norm_num : (1045094400 : ℕ) ≠ 0)).mpr hHdiv
    have hconstant :
        (1045094400 : ℕ).factorization 2 = 13 := by
      rw [show 1045094400 =
          2 ^ 13 * 127575 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simpa only [hconstant] using hle 2
  have hHfactorizationGe :
      13 ≤ (Nat.card H).factorization 2 :=
    (show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
      hHne |>.mp htwoThirteenth
  have hHfactorization :
      (Nat.card H).factorization 2 = 13 := by
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
  have hHindex : H.index = 5100480 := by
    change (fixingSubgroup P s).index = 5100480
    omega
  have hHindexCard := H.index_mul_card
  have hPcard :
      Nat.card P = 5100480 * Nat.card H := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hindexFactorization :
      (5100480 : ℕ).factorization 2 = 6 := by
    rw [show 5100480 = 2 ^ 6 * 79695 by norm_num,
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

theorem five_point_stabilizer_card_dvd_without_two_thirteenth
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) ∣ 522547200 := by
  let H : Subgroup P := fixingSubgroup P s
  have hHne : Nat.card H ≠ 0 :=
    Nat.card_pos.ne'
  have hdiv : Nat.card H ∣ 1045094400 := by
    simpa only [H] using
      five_point_stabilizer_card_dvd_without_two_fourteenth
        X P hcard h5 hnotAlt s hs
  have hnotTwoThirteenth : ¬2 ^ 13 ∣ Nat.card H := by
    simpa only [H] using
      two_thirteenth_not_dvd_five_point_stabilizer_of_not_alternating
        X P hcard h5 hnotAlt s hs
  apply
    (Nat.factorization_le_iff_dvd hHne
      (by norm_num : (522547200 : ℕ) ≠ 0)).mp
  intro p
  have hle :=
    ((Nat.factorization_le_iff_dvd hHne
      (by norm_num : (1045094400 : ℕ) ≠ 0)).mpr hdiv) p
  by_cases hp : p = 2
  · subst p
    have hfactorizationLt :
        (Nat.card H).factorization 2 < 13 := by
      rw [← not_le]
      intro hthirteen
      exact hnotTwoThirteenth
        ((show Nat.Prime 2 by norm_num).pow_dvd_iff_le_factorization
          hHne |>.mpr hthirteen)
    have htarget :
        (522547200 : ℕ).factorization 2 = 12 := by
      rw [show 522547200 =
          2 ^ 12 * 127575 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization_pow,
        Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [htarget]
    omega
  · have horiginal :
        (1045094400 : ℕ).factorization p =
          (522547200 : ℕ).factorization p := by
      have hp' : 2 ≠ p := Ne.symm hp
      rw [show 1045094400 =
          2 * 522547200 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num),
        Finsupp.add_apply,
        (show Nat.Prime 2 by norm_num).factorization,
        Finsupp.single_apply]
      simp [hp']
    rwa [← horiginal]

end FiveTransitive.Degree24

end CFSG
