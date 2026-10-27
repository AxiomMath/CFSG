module

public import CFSG.Permutation.FiveTransitive.Degree18SevenCycle
public import Mathlib.CategoryTheory.Action.Concrete

public section

namespace CFSG

namespace FiveTransitive.Degree18

open MulAction SubMulAction Subgroup

private theorem orderOf_ne_fortyNine
    (X : Type) [Fintype X] [DecidableEq X]
    (hcard : Fintype.card X = 18) (g : Equiv.Perm X) :
    orderOf g ≠ 49 := by
  intro horder
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcycleLength :
      ∀ c ∈ g.cycleType, c = 7 := by
    intro c hc
    have hdvd : c ∣ 49 := by
      rw [← horder]
      exact Equiv.Perm.dvd_of_mem_cycleType hc
    have htwo : 2 ≤ c :=
      Equiv.Perm.two_le_of_mem_cycleType hc
    have hle : c ≤ 18 := by
      calc
        c ≤ g.support.card :=
          Equiv.Perm.le_card_support_of_mem_cycleType hc
        _ ≤ Fintype.card X := Finset.card_le_univ g.support
        _ = 18 := hcard
    have hdvd' : c ∣ 7 ^ 2 := by
      norm_num
      exact hdvd
    obtain ⟨k, hk, hck⟩ :=
      (Nat.dvd_prime_pow (by norm_num)).mp hdvd'
    rw [hck] at htwo hle ⊢
    interval_cases k
    all_goals norm_num at *
  have hpow : g ^ 7 = 1 :=
    Equiv.Perm.pow_prime_eq_one_iff.mpr hcycleLength
  have hdvd : orderOf g ∣ 7 :=
    orderOf_dvd_of_pow_eq_one hpow
  rw [horder] at hdvd
  norm_num at hdvd

private theorem nonidentity_sylowSeven_fixed_points_of_card_fortyNine
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 18)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S : Sylow 7 P) (hScard : Nat.card S = 49)
    (u : S) (hu : u ≠ 1) :
    Fintype.card (MulAction.fixedBy X u) = 4 := by
  classical
  have huOrderDvd : orderOf u ∣ 49 := by
    rw [← hScard, Nat.card_eq_fintype_card]
    exact orderOf_dvd_card
  have huOrderNeOne : orderOf u ≠ 1 := by
    intro huOrder
    apply hu
    exact orderOf_eq_one_iff.mp huOrder
  let g : Equiv.Perm X := ((u : S) : P)
  have hgOrderEq : orderOf g = orderOf u := by
    calc
      orderOf g = orderOf (u : P) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
  have huOrderNeFortyNine : orderOf u ≠ 49 := by
    intro huOrder
    apply orderOf_ne_fortyNine X hcard g
    rw [hgOrderEq, huOrder]
  have huOrder : orderOf u = 7 := by
    have huOrderDvd' : orderOf u ∣ 7 ^ 2 := by
      norm_num
      exact huOrderDvd
    obtain ⟨k, hk, huOrderEq⟩ :=
      (Nat.dvd_prime_pow (by norm_num)).mp huOrderDvd'
    rw [huOrderEq] at huOrderNeOne huOrderNeFortyNine ⊢
    interval_cases k
    all_goals norm_num at *
  have hgOrder : orderOf g = 7 := hgOrderEq.trans huOrder
  have hgPrime : (orderOf g).Prime := by
    rw [hgOrder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgPrime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgOrder] at hsum
  have hsupportLe : g.support.card ≤ 18 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ g.support
      _ = 18 := hcard
  have hmTwo : m + 1 = 2 := by
    have hmLe : m + 1 ≤ 2 := by
      nlinarith
    rcases (show m + 1 = 1 ∨ m + 1 = 2 by omega) with hmOne | hmTwo
    · have hcycle : g.IsCycle := by
        rw [← Equiv.Perm.card_cycleType_eq_one, hm, hmOne]
        simp
      have hsupport : g.support.card = 7 := by
        omega
      exact (hnotAlt
        (alternatingGroup_le_of_sevenCycle
          X P hcard h5 (show g ∈ P from (u : P).prop)
            hcycle hsupport)).elim
    · exact hmTwo
  have hsupport : g.support.card = 14 := by
    omega
  have hfixed :
      Fintype.card (MulAction.fixedBy X u) =
        Fintype.card X - g.support.card := by
    have hs :
        MulAction.fixedBy X u =
          {x : X | x ∉ g.support} := by
      ext x
      change g x = x ↔ x ∉ g.support
      exact Equiv.Perm.notMem_support.symm
    calc
      Fintype.card (MulAction.fixedBy X u) =
          Fintype.card {x : X // x ∉ g.support} :=
        Fintype.card_congr (Set.equivOfEq hs)
      _ = Fintype.card X - g.support.card := by
        rw [Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hfixed, hcard, hsupport]

private theorem sylowSeven_card_ne_fortyNine
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 18)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S : Sylow 7 P) :
    Nat.card S ≠ 49 := by
  classical
  intro hScard
  have hfixedOne :
      Fintype.card (MulAction.fixedBy X (1 : S)) = 18 := by
    calc
      Fintype.card (MulAction.fixedBy X (1 : S)) =
          Fintype.card (Set.univ : Set X) :=
        Fintype.card_congr
          (Set.equivOfEq
            (MulAction.fixedBy_one_eq_univ (M := S) (α := X)))
      _ = Fintype.card X :=
        Fintype.card_congr (Equiv.Set.univ X)
      _ = 18 := hcard
  have hfixed (u : S) :
      Fintype.card (MulAction.fixedBy X u) =
        if u = 1 then 18 else 4 := by
    by_cases hu : u = 1
    · subst u
      rw [if_pos rfl]
      exact hfixedOne
    · rw [if_neg hu]
      exact nonidentity_sylowSeven_fixed_points_of_card_fortyNine
        X P hcard h5 hnotAlt S hScard u hu
  have hsum :
      (∑ u : S, Fintype.card (MulAction.fixedBy X u)) =
        18 + (Fintype.card S - 1) * 4 := by
    have hone : (1 : S) ∈ (Finset.univ : Finset S) :=
      Finset.mem_univ _
    have herase :
        (∑ u ∈ (Finset.univ : Finset S).erase 1,
            Fintype.card (MulAction.fixedBy X u)) =
          ((Finset.univ : Finset S).erase 1).card * 4 := by
      calc
        (∑ u ∈ (Finset.univ : Finset S).erase 1,
            Fintype.card (MulAction.fixedBy X u)) =
            ∑ _u ∈ (Finset.univ : Finset S).erase 1, 4 := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [hfixed, if_neg (Finset.ne_of_mem_erase hu)]
        _ = ((Finset.univ : Finset S).erase 1).card * 4 := by
          simp
    calc
      (∑ u : S, Fintype.card (MulAction.fixedBy X u)) =
          (∑ u ∈ (Finset.univ : Finset S).erase 1,
              Fintype.card (MulAction.fixedBy X u)) +
            Fintype.card (MulAction.fixedBy X (1 : S)) := by
        exact (Finset.sum_erase_add _ _ hone).symm
      _ = ((Finset.univ : Finset S).erase 1).card * 4 + 18 := by
        rw [herase, hfixedOne]
      _ = 18 + (Fintype.card S - 1) * 4 := by
        rw [Finset.card_erase_of_mem hone, Finset.card_univ]
        change (Fintype.card S - 1) * 4 + 18 =
          18 + (Fintype.card S - 1) * 4
        omega
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group S X
  rw [hsum, show Fintype.card S = 49 by
    rw [← Nat.card_eq_fintype_card]
    exact hScard] at hburnside
  omega

private theorem seven_dvd_card_of_five_transitive
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 18)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i) :
    7 ∣ Nat.card P := by
  classical
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  obtain ⟨s, _, hs⟩ :=
    Set.exists_subset_card_eq
      (s := (Set.univ : Set X)) (n := 5) (by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
        omega)
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hindex :
      (fixingSubgroup P s).index = 1028160 := by
    omega
  have hindexCard := (fixingSubgroup P s).index_mul_card
  rw [hindex] at hindexCard
  rw [← hindexCard]
  exact dvd_mul_of_dvd_left (by norm_num) _

theorem sylowSeven_card_eq_seven
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 18)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S : Sylow 7 P) :
    Nat.card S = 7 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hsevenDvd : 7 ∣ Nat.card P :=
    seven_dvd_card_of_five_transitive X P hcard h5
  have hpositive :
      0 < (Nat.card P).factorization 7 :=
    Nat.prime_seven.factorization_pos_of_dvd Nat.card_pos.ne' hsevenDvd
  have hPdvd :
      Nat.card P ∣ (18 : ℕ).factorial := by
    have hdvd := P.card_subgroup_dvd_card
    rw [Nat.card_perm] at hdvd
    rw [Nat.card_eq_fintype_card]
    simpa only [Nat.card_eq_fintype_card, hcard] using hdvd
  have hfactorizationLe :
      (Nat.card P).factorization 7 ≤ 2 := by
    have hle :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (by norm_num : (18 : ℕ).factorial ≠ 0)).mpr hPdvd
    have hleSeven := hle 7
    have hfactorial :
        ((18 : ℕ).factorial).factorization 7 = 2 := by
      rw [show (18 : ℕ).factorial =
          7 * (7 * 130660687872000) by norm_num,
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
  have hcases :
      (Nat.card P).factorization 7 = 1 ∨
        (Nat.card P).factorization 7 = 2 := by
    omega
  rcases hcases with hone | htwo
  · rw [S.card_eq_multiplicity, hone]
    norm_num
  · exfalso
    apply sylowSeven_card_ne_fortyNine X P hcard h5 hnotAlt S
    rw [S.card_eq_multiplicity, htwo]
    norm_num

end FiveTransitive.Degree18

end CFSG
