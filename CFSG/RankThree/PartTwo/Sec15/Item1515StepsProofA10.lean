module

public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofTools
import CFSG.RankThree.PartTwo.KFacts.KS14MultCore
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1515

open Equiv

@[expose] def a10xP : Perm (Fin 10) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

@[expose] def a10yP : Perm (Fin 10) :=
  swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * (swap 5 6 * swap 6 7 * swap 7 8 * swap 8 9)

@[expose] def a10gP : Perm (Fin 10) := swap 1 4 * swap 2 3

@[expose] def a10x : alternatingGroup (Fin 10) :=
  ⟨a10xP, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩

@[expose] def a10y : alternatingGroup (Fin 10) :=
  ⟨a10yP, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩

@[expose] def a10g : alternatingGroup (Fin 10) :=
  ⟨a10gP, by rw [Perm.mem_alternatingGroup]; decide +kernel⟩

theorem a10_relations : a10xP ^ 5 = 1 ∧ a10yP ^ 5 = 1 ∧ a10xP * a10yP = a10yP * a10xP ∧
    a10gP * a10xP * a10gP⁻¹ = a10xP ^ 4 ∧ a10gP * a10yP * a10gP⁻¹ = a10xP ^ 3 * a10yP := by
  decide +kernel

theorem a10x_pow_five : a10x ^ 5 = 1 := Subtype.ext a10_relations.1

theorem a10y_pow_five : a10y ^ 5 = 1 := Subtype.ext a10_relations.2.1

theorem a10x_mul_comm : a10x * a10y = a10y * a10x := Subtype.ext a10_relations.2.2.1

theorem a10g_conj_x : a10g * a10x * a10g⁻¹ = a10x ^ 4 := Subtype.ext a10_relations.2.2.2.1

theorem a10g_conj_y : a10g * a10y * a10g⁻¹ = a10x ^ 3 * a10y :=
  Subtype.ext a10_relations.2.2.2.2

theorem a10_values : a10xP 0 ≠ 0 ∧ a10yP 0 ≠ 0 ∧ a10xP 5 = 5 ∧ a10yP 5 ≠ 5 := by
  decide +kernel

theorem orderOf_a10x : orderOf a10x = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine orderOf_eq_prime a10x_pow_five fun h => a10_values.1 ?_
  have := congrArg (fun σ : alternatingGroup (Fin 10) => (σ : Perm (Fin 10)) 0) h
  exact this

theorem orderOf_a10y : orderOf a10y = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine orderOf_eq_prime a10y_pow_five fun h => a10_values.2.1 ?_
  have := congrArg (fun σ : alternatingGroup (Fin 10) => (σ : Perm (Fin 10)) 0) h
  exact this

theorem a10y_not_mem_zpowers : a10y ∉ Subgroup.zpowers a10x := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
  have h1 : ((a10x ^ k : alternatingGroup (Fin 10)) : Perm (Fin 10)) 5 = 5 := by
    rw [Subgroup.coe_zpow]
    exact Perm.zpow_apply_eq_self_of_apply_eq_self a10_values.2.2.1 k
  rw [hk] at h1
  exact a10_values.2.2.2 h1

theorem card_closure_a10 : Nat.card (Subgroup.closure ({a10x, a10y} : Set _)) = 25 := by
  have hcl : Subgroup.closure ({a10x, a10y} : Set (alternatingGroup (Fin 10))) =
      Subgroup.zpowers a10x ⊔ Subgroup.zpowers a10y := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
      Subgroup.zpowers_eq_closure]
  have hC : Subgroup.zpowers a10y ≤ Subgroup.centralizer (Subgroup.zpowers a10x : Set _) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left a10x_mul_comm k).eq
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (hC.trans (Subgroup.centralizer_le_normalizer _))
  have hx5 : Nat.card (Subgroup.zpowers a10x) = 5 := by rw [Nat.card_zpowers, orderOf_a10x]
  have hy5 : Nat.card (Subgroup.zpowers a10y) = 5 := by rw [Nat.card_zpowers, orderOf_a10y]
  have hinf : Nat.card (Subgroup.zpowers a10x ⊓ Subgroup.zpowers a10y : Subgroup _) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers a10x ⊓ Subgroup.zpowers a10y : Subgroup _) ∣ 5 :=
      hy5 ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
    · exact h1
    · exfalso
      have hle : Subgroup.zpowers a10y ≤ Subgroup.zpowers a10x := by
        have heq : Subgroup.zpowers a10x ⊓ Subgroup.zpowers a10y = Subgroup.zpowers a10y :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h5, hy5])
        rw [← heq]
        exact inf_le_left
      exact a10y_not_mem_zpowers (hle (Subgroup.mem_zpowers a10y))
  rw [hcl]
  rw [hinf, hx5, hy5, mul_one] at hprod
  exact hprod

theorem factorization_card_a10 : (Nat.card (alternatingGroup (Fin 10))).factorization 5 = 2 := by
  rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2,
    show (1814400 : ℕ) = 5 ^ 2 * 72576 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow (by norm_num),
    Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd (by norm_num),
    add_zero]

theorem not_sq_dvd_card_a10 {p : ℕ} (hp : p.Prime) (hp6 : Nat.Coprime 6 p) (hp5 : p ≠ 5) :
    ¬ p ^ 2 ∣ 1814400 := by
  intro h
  have hd : p ∣ 2 ^ 7 * 3 ^ 4 * 5 ^ 2 * 7 := (dvd_pow_self p two_ne_zero).trans (by simpa using h)
  have h2 : ¬ p ∣ 2 := fun h2 => by
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    subst this
    norm_num at hp6
  have h3 : ¬ p ∣ 3 := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    subst this
    norm_num at hp6
  have h5 : ¬ p ∣ 5 := fun h5 => hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5)
  rcases (Nat.Prime.dvd_mul hp).mp hd with hd | h7
  · rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd5
    · rcases (Nat.Prime.dvd_mul hp).mp hd with hd2 | hd3
      · exact h2 (hp.dvd_of_dvd_pow hd2)
      · exact h3 (hp.dvd_of_dvd_pow hd3)
    · exact h5 (hp.dvd_of_dvd_pow hd5)
  · have := (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 7)).mp h7
    subst this
    norm_num at h

theorem multFree_alternatingGroup_ten : MultFree (alternatingGroup (Fin 10)) := by
  intro X _ _ Z _ hX hZc hcop ⟨e⟩
  have : Group.IsPerfect X := hX
  refine KFacts.KS14.eq_bot_of_isPerfect_of_sylow_comm hZc fun p hp hpZ P => ?_
  have : Fact p.Prime := ⟨hp⟩
  have hp6 : Nat.Coprime 6 p := (Nat.Coprime.coprime_dvd_right hpZ hcop)
  by_cases hp5 : p = 5
  · subst hp5
    exact KFacts.KS14.sylow_five_comm_of_witness hZc e a10x_pow_five a10x_mul_comm a10g_conj_x
      a10g_conj_y card_closure_a10 factorization_card_a10 P
  · refine KFacts.KS14.sylow_comm_of_not_sq_dvd hZc ?_ P
    rw [Nat.card_congr e.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2]
    exact not_sq_dvd_card_a10 hp hp6 hp5

end CFSG.RankThree.PartTwo.Sec15.Proof1515
