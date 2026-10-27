module

public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.Theta.SolvableLocalQuotientAlpha
public import CFSG.RankThree.PartTwo.Source.SolvableNormalizedTwoCore

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (aschCore)
open scoped Pointwise

section Hyperplanes

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem card_zpowers_eq_three {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) : Nat.card (Subgroup.zpowers a) = 3 := by
  rw [Nat.card_zpowers]
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (hA.2 a ha)) with
    h | h
  · exact absurd (orderOf_eq_one_iff.mp h) ha1
  · exact h

theorem exists_hyperplane_of_mem {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {a x : G} (ha : a ∈ A) (hx : x ∈ A) :
    ∃ D : Subgroup G, D ≤ A ∧ Nat.card D = 9 ∧ a ∈ D ∧ x ∈ D := by
  set H := Subgroup.zpowers a ⊔ Subgroup.zpowers x with hHdef
  have hHA : H ≤ A := sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hx)
  have hax : a * x = x * a := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨x, hx⟩)
  have hcomm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    refine (Subgroup.zpowers_le.mpr ?_).trans
      (Subgroup.centralizer_le_normalizer (Subgroup.zpowers x : Set G))
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨k, rfl⟩
    exact (Commute.zpow_left hax.symm k).eq
  have hmul := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcomm
  have hle3 : ∀ y ∈ A, Nat.card (Subgroup.zpowers y) ≤ 3 := fun y hy => by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hA.2 y hy))
  have hcard9 : Nat.card H ≤ 9 := by
    have h1 : Nat.card H =
        Nat.card ((Subgroup.zpowers a : Set G) * (Subgroup.zpowers x : Set G)) := by
      rw [← hmul]
      rfl
    rw [h1]
    refine (Set.natCard_mul_le).trans ?_
    have h2 := hle3 a ha
    have h3 := hle3 x hx
    exact (Nat.mul_le_mul h2 h3).trans (by norm_num)
  have hdvd27 : Nat.card H ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_dvd_of_le hHA
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd27
  have hk2 : k ≤ 2 := by
    by_contra hk2
    have : k = 3 := by omega
    rw [hk, this] at hcard9
    norm_num at hcard9
  have hH9 : Nat.card H ∣ 3 ^ 2 := hk ▸ Nat.pow_dvd_pow 3 hk2
  obtain ⟨D, hD9, hHD, hDA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_three hH9
    (by rw [h27]; norm_num) hHA
  exact ⟨D, hDA, by rw [hD9]; norm_num,
    hHD (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)),
    hHD (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))⟩

theorem commutator_theta_eq_bot {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hα : ∀ D : Subgroup G, D ≤ A → Nat.card D = 9 → thetaAlpha 3 D = ⊥) :
    ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)), A⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨D, hDA, hD9, haD, hxD⟩ := exists_hyperplane_of_mem hA h27 ha hx
  have hJ : ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)), D⁆ ≤
      thetaJ 3 D := by
    unfold thetaJ
    exact le_iSup_of_le a (le_iSup_of_le haD (le_iSup_of_le ha1 le_rfl))
  have hbot : ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)), D⁆ =
      ⊥ := eq_bot_iff.mpr (hJ.trans ((le_sup_left : thetaJ 3 D ≤ thetaJ 3 D ⊔ thetaT 3 D).trans
        (hα D hDA hD9).le))
  have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hu
  rw [Subgroup.mem_centralizer_iff] at hc
  exact hc x hxD

end Hyperplanes

theorem omegaA_nonempty {G : Type} [Group G] [Finite G] (hG : PartTwoStanding G)
    (hS : partTwoS G = ∅) {A : Subgroup G} (hAF : A ∈ partTwoF G) (hAT : A ∉ partTwoT G) :
    (omegaA A).Nonempty := by
  have hAE : A ∈ partTwoE G := (hG.toTheoremFourHyp.partTwoF_eq_partTwoE hS).1 ▸ hAF
  have hAab := hAE.1
  have h27 := hAE.2.1
  by_contra hne
  have hstar : ∀ a ∈ A, a ≠ 1 → StarConditionAt A a := by
    intro a ha ha1
    by_contra h
    exact hne ⟨_, zpowers_mem_omegaA_iff.mpr ⟨ha, card_zpowers_eq_three hAab ha ha1, h⟩⟩
  obtain ⟨hsolv, hindep, hnorm⟩ :=
    CFSG.RankThree.Theta.part_two_solvable_local_quotient_alpha_criterion A hAab h27 hstar
  obtain ⟨B, hBA, hB9, -, -⟩ := exists_hyperplane_of_mem hAab h27 A.one_mem A.one_mem
  by_cases hX : thetaAlpha 3 B = ⊥
  · have hα : ∀ D : Subgroup G, D ≤ A → Nat.card D = 9 → thetaAlpha 3 D = ⊥ :=
      fun D hDA hD9 => (hindep D B hDA hD9 hBA hB9).trans hX
    have hmem : A ∈ partTwoS G := by
      refine ⟨hAF, fun a ha ha1 => ?_, fun D hDA hD9 => ?_⟩
      · rw [commutator_theta_eq_bot hAab h27 ha ha1 hα, Subgroup.card_bot]
        exact odd_one
      · have hT : thetaT 3 D = ⊥ := eq_bot_iff.mpr
          ((le_sup_right : thetaT 3 D ≤ thetaJ 3 D ⊔ thetaT 3 D).trans (hα D hDA hD9).le)
        rw [hT, Subgroup.card_bot]
        exact odd_one
    rw [hS] at hmem
    exact hmem
  · have h3 : ¬ 3 ∣ Nat.card (thetaAlpha 3 B) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (hsolv B hBA hB9).2
    exact hAT (Source.rank3II_6_2 hG.charTwoType hG.localRank_lt hAE hX (hsolv B hBA hB9).1 h3
      (hnorm B hBA hB9)).2

end CFSG.RankThree.PartTwo.Sec13
