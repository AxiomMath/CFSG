module

public import CFSG.Permutation.FiveTransitive.Degree28TwoGroupReduction
public import CFSG.Permutation.FiveTransitive.Degree28ThirteenCentralizer
public import CFSG.Permutation.FiveTransitive.Degree28ThirteenArithmetic
public import CFSG.Permutation.FiveTransitive.Degree28ThirteenEven

public section

namespace CFSG

namespace FiveTransitive.Degree28ThirteenReduction

open MulAction

private theorem card_and_exponent
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ 9 ∧ Nat.card (fixingSubgroup P s) = 2 ^ a ∧
      Nat.card P = 11793600 * 2 ^ a := by
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp
    (Degree28TwoGroupReduction.is_two_group P hcard h5 hnotAlt s hs)
  obtain ⟨hlo,hhi⟩ := Degree28TwoGroupReduction.card_bounds P hcard h5 hnotAlt s hs
  rw [ha] at hlo hhi
  have hapos : 1 ≤ a := by
    by_contra hn
    have haz : a = 0 := by omega
    simp [haz] at hlo
  have hale : a ≤ 9 := by
    by_contra hn
    have hpow := Nat.pow_le_pow_right (by norm_num : 0 < 2) (show 10 ≤ a by omega)
    norm_num at hpow
    omega
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq s (by rwa [hs])
  rw [Nat.card_eq_fintype_card,hcard,hs] at hi
  norm_num at hi
  have hm := (fixingSubgroup P s).index_mul_card
  rw [hi,ha] at hm
  exact ⟨a,hapos,hale,ha,hm.symm⟩

private theorem sylow_card
    (K : Type) [Group K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 11793600 * 2 ^ a) (S : Sylow 13 K) : Nat.card S = 13 := by
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hc : (11793600 : ℕ).factorization 13 = 1 := by
    rw [show 11793600 = 13 * 907200 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      (show Nat.Prime 13 by norm_num).factorization, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [S.card_eq_multiplicity,hK,
    Nat.factorization_mul (by norm_num) (pow_ne_zero _ (by norm_num)),
    Finsupp.add_apply,hc,Nat.factorization_pow,Finsupp.smul_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 13 ∣ 2)]
  norm_num

private theorem sylow_fixed_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (S : Sylow 13 P) (hS : Nat.card S = 13) : Nat.card (fixedPoints S X) = 2 := by
  classical
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let _ : IsCyclic S := isCyclic_of_prime_card hS
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hup : orderOf (u.val : P) = 13 := (Subgroup.orderOf_coe u).trans (hu.trans hS)
  have hct := Degree28ThirteenCentralizer.order_thirteen_cycle_type
    P hcard h5 hnotAlt u.val hup
  have hsub : fixedPoints S X ⊆ Function.fixedPoints u.val.val := by
    intro x hx
    exact mem_fixedPoints.mp hx u
  have hle := Set.ncard_le_ncard hsub
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card (α := Function.fixedPoints u.val.val),
    Equiv.Perm.card_fixedPoints,hct,hcard] at hle
  change Nat.card (fixedPoints S X) ≤ 2 at hle
  have hm := S.isPGroup'.card_modEq_card_fixedPoints X
  change Nat.card X % 13 = Nat.card (fixedPoints S X) % 13 at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  omega

theorem five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    Nat.card (fixingSubgroup P s) = 4 ∨ Nat.card (fixingSubgroup P s) = 8 ∨
      Nat.card (fixingSubgroup P s) = 16 := by
  classical
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let _ : Fintype P := Fintype.ofFinite P
  let _ : IsMultiplyPretransitive P X 5 := h5
  let _ : IsPretransitive P X := is_one_pretransitive_iff.mp
    (isMultiplyPretransitive_of_le (G := P) (α := X) (n := 5)
      (by norm_num : 1 ≤ 5) (by simp [hcard]))
  obtain ⟨a,ha,ha',hH,hP⟩ := card_and_exponent P hcard h5 hnotAlt s hs
  let S : Sylow 13 P := Sylow.nonempty.some
  have hS := sylow_card P hP S
  have hCdvd := Degree28ThirteenCentralizer.centralizer_card_dvd P hcard h5 hnotAlt S hS
  let C : Subgroup P := Subgroup.centralizer (S : Set P)
  let N : Subgroup P := Subgroup.normalizer (S : Set P)
  have hCgcd : Nat.card C ∣ Nat.gcd 338 (11793600 * 2 ^ a) := by
    apply Nat.dvd_gcd hCdvd
    rw [← hP]
    exact C.card_subgroup_dvd_card
  have hgcd : Nat.gcd 338 (11793600 * 2 ^ a) = 26 := by
    interval_cases a <;> norm_num
  have hC : Nat.card C ∣ 13 * 2 := by simpa [hgcd] using hCgcd
  obtain ⟨hc,hr,hcpos,hrpos,hmod,hproduct⟩ :=
    Degree28ThirteenArithmetic.sylow_thirteen_normalizer_constraints_of_centralizer_card_dvd
      P 2 S hS hC
  let c := (S : Subgroup P).relIndex C
  let r := C.relIndex N
  change c ∣ 2 at hc
  change r ∣ 12 at hr
  change 0 < c at hcpos
  change 0 < r at hrpos
  change N.index % 13 = 1 at hmod
  change c * r * N.index * 13 = Nat.card P at hproduct
  have hNcard : Nat.card N = c * r * 13 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < N.index from Nat.pos_of_ne_zero
      Subgroup.index_ne_zero_of_finite)
    calc
      N.index * Nat.card N = Nat.card P := N.index_mul_card
      _ = N.index * (c * r * 13) := by rw [← hproduct]; ring
  have hevenN := Degree28ThirteenEven.normalizer_even P X S
    (sylow_fixed_card P hcard h5 hnotAlt S hS)
  change 2 ∣ Nat.card N at hevenN
  rw [hNcard] at hevenN
  have heven : 2 ∣ c * r := by
    rcases Nat.prime_two.dvd_mul.mp hevenN with h | h
    · exact h
    · norm_num at h
  rw [hP] at hproduct
  have haCases := Degree28ThirteenArithmetic.exponent_cases ha ha' hc hr hcpos hrpos
    heven hmod hproduct
  rw [hH]
  rcases haCases with rfl | rfl | rfl <;> norm_num

end FiveTransitive.Degree28ThirteenReduction

end CFSG
