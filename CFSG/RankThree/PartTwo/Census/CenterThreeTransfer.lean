module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SmallSylowCentralCover

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

namespace CenterThreeTransfer

theorem pow_prime_eq_one_of_card_eq_sq {Q : Type*} [Group Q] {p : ℕ} [hp : Fact p.Prime]
    (hQ : Nat.card Q = p ^ 2) (hcyc : ¬ IsCyclic Q) (x : Q) : x ^ p = 1 := by
  have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQ]; exact pow_ne_zero 2 hp.out.ne_zero)
  obtain ⟨m, hm, hx⟩ := (Nat.dvd_prime_pow hp.out).1 (hQ ▸ orderOf_dvd_natCard x)
  interval_cases m
  · rw [pow_zero, orderOf_eq_one_iff] at hx
    rw [hx, one_pow]
  · rw [pow_one] at hx
    rw [← hx, pow_orderOf_eq_one]
  · exact absurd (isCyclic_of_orderOf_eq_card x (hx.trans hQ.symm)) hcyc

theorem card_center_dvd_three_of_factorization {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] (hZ : IsPGroup 3 (Subgroup.center X))
    (hfac : (Nat.card (X ⧸ Subgroup.center X)).factorization 3 = 2) :
    Nat.card (Subgroup.center X) ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hker : f.ker = Subgroup.center X := QuotientGroup.ker_mk' _
  obtain ⟨C⟩ : Nonempty (Sylow 3 f.ker) := inferInstance
  obtain ⟨Q⟩ : Nonempty (Sylow 3 (X ⧸ Subgroup.center X)) := inferInstance
  have hkerP : IsPGroup 3 f.ker := by
    rw [hker]
    exact hZ
  have hC : Nat.card (C : Subgroup f.ker) = Nat.card (Subgroup.center X) := by
    rw [← C.is_maximal' (hkerP.to_subgroup ⊤) le_top, Subgroup.card_top, hker]
  have hQ : Nat.card (Q : Subgroup (X ⧸ Subgroup.center X)) = 3 ^ 2 := by
    rw [Q.card_eq_multiplicity, hfac]
  by_cases hcyc : IsCyclic (Q : Subgroup (X ⧸ Subgroup.center X))
  · have h := CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot f hsurj
      hker.le C Q hcyc
    rw [← hC, h, Subgroup.card_bot]
    exact one_dvd 3
  · have helem : CFSG.Open.IsElemAbelian 3 (Q : Subgroup (X ⧸ Subgroup.center X)) :=
      ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ, fun x hx =>
        congrArg Subtype.val (pow_prime_eq_one_of_card_eq_sq hQ hcyc ⟨x, hx⟩)⟩
    have hle := (CFSG.ShultStronglyClosedTI.central_cover_elementary_rank_two_sylow_kernel_bound
      f hsurj hker.le C Q helem hQ).2
    rw [hC] at hle
    obtain ⟨k, hk⟩ := hZ.exists_card_eq
    rw [hk] at hle ⊢
    rcases k with _ | _ | k
    · exact one_dvd 3
    · exact dvd_rfl
    · have h9 : 3 ^ 2 ≤ 3 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

theorem card_center_dvd_three {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
    (hZ : IsPGroup 3 (Subgroup.center X)) {m : ℕ}
    (hcard : Nat.card (X ⧸ Subgroup.center X) = 9 * m) (hm : ¬ 3 ∣ m) :
    Nat.card (Subgroup.center X) ∣ 3 := by
  refine card_center_dvd_three_of_factorization hZ ?_
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  rw [hcard, show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.factorization_mul (by norm_num) hm0,
    Nat.factorization_pow]
  simp [Nat.prime_three.factorization_self, Nat.factorization_eq_zero_of_not_dvd hm]

theorem card_center_dvd_three_of_mulEquiv {X S : Type*} [Group X] [Finite X] [Group S]
    (hX : IsQuasisimple X) (hZ : IsPGroup 3 (Subgroup.center X))
    (e : X ⧸ Subgroup.center X ≃* S) {m : ℕ} (hS : Nat.card S = 9 * m) (hm : ¬ 3 ∣ m) :
    Nat.card (Subgroup.center X) ∣ 3 := by
  have : Group.IsPerfect X := hX.1
  exact card_center_dvd_three hZ ((Nat.card_congr e.toEquiv).trans hS) hm

end CenterThreeTransfer

end CFSG.RankThree.PartTwo.Sec4.Census
