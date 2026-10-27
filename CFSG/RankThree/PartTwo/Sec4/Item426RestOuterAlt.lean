module

public import CFSG.RankThree.PartTwo.Sec4.Item426RestModels
public import CFSG.RankThree.PartTwo.Sec4.Item47WStatement
import CFSG.RankThree.PartTwo.Sec4.Item426RestOuter
import CFSG.RankThree.PartTwo.Sec4.Item426A6Outer

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item426Rest

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def OuterFieldSL (X : Type) [Group X] (P : Subgroup X) (j : ℕ) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (3 * j) ∧
      Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K)) ∧
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀), Nat.card K₀ = 2 ^ j ∧
      Nonempty (P ⧸ aschbacherSolvableCore 3 P ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K₀)

@[expose] def OuterFieldSU (X : Type) [Group X] (P : Subgroup X) (j : ℕ) : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ (3 * j)) ^ 2 ∧
      Nonempty (X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ (3 * j)) K)) ∧
    ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀), Nat.card K₀ = (2 ^ j) ^ 2 ∧
      Nonempty (P ⧸ aschbacherSolvableCore 3 P ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ j) K₀)

theorem exists_eq_pow_of_cube {p n c : ℕ} (hp : p.Prime) (h : c ^ 3 = p ^ n) :
    ∃ i, c = p ^ i ∧ 3 * i = n := by
  have hdvd : c ∣ p ^ n := ⟨c ^ 2, by rw [← h]; ring⟩
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨i, rfl, ?_⟩
  rw [← pow_mul] at h
  have := Nat.pow_right_injective hp.two_le h
  omega

theorem mod_three_of_center_statedSU {X : Type} [Group X] {m : ℕ} (hm : 2 ≤ m) {K : Type}
    [Field K] [Finite K] (hKc : Nat.card K = (2 ^ m) ^ 2)
    (e : X ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K)
    (h3 : 3 ∣ Nat.card (Subgroup.center X)) : 2 ^ m % 3 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnq : ((3 : ℕ), 2 ^ m) ≠ (3, 2) := fun h' => by
    have h2 : (2 : ℕ) ^ m = 2 := (Prod.mk.inj h').2
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  obtain ⟨-, hZ⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hKc le_rfl hnq
  have hc : (Subgroup.center X).map (e : X →* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K) =
      Subgroup.center _ := Subgroup.map_center_eq e
  have hcard : Nat.card (Subgroup.center X) = Nat.gcd 3 (2 ^ m + 1) := by
    rw [← Subgroup.card_map_of_injective
        (f := (e : X →* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ m) K)) e.injective, hc, hZ,
      (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hKc (n := 3) (by norm_num)).2.2]
  rw [hcard] at h3
  have h3' : 3 ∣ 2 ^ m + 1 := h3.trans (Nat.gcd_dvd_right 3 _)
  omega

theorem three_ne_zero_of_card {K : Type} [Field K] [Finite K] {p n : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hK : Nat.card K = p ^ n) : (3 : K) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  exact Item426.Config426.three_ne_zero_of_charP hp hp3

theorem two_pow_two_mul_mod_three (m : ℕ) : 2 ^ (2 * m) % 3 = 1 := by
  rw [pow_mul, Nat.pow_mod]
  norm_num

namespace ConfigRest

variable {X : Type} [Group X] [Finite X] {α : MulAut X} {P : Subgroup X}

theorem outer_SL_card (h : ConfigRest X α P) (hout : ¬ IsInnerAut α) {K : Type} [Field K]
    [Finite K] {p n : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hK : Nat.card K = p ^ n)
    (e : X ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K) :
    ∃ j, 3 * j = n ∧ ∃ (K₀ : Type) (_ : Field K₀) (_ : Finite K₀), Nat.card K₀ = p ^ j ∧
      Nonempty (P ⧸ aschbacherSolvableCore 3 P ≃* CFSG.Assembly.LowTwoRank.StatedSL 3 K₀) := by
  obtain ⟨σ, hσo, ⟨eP⟩⟩ := h.outer_SL hout (three_ne_zero_of_card hp hp3 hK)
    (e.trans (statedSLEquiv 3 K))
  have hc := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
  rw [hσo, hK] at hc
  obtain ⟨j, hj, hj3⟩ := exists_eq_pow_of_cube hp hc
  exact ⟨j, hj3, CFSG.GH74.GLS.IVK.fixedField σ, inferInstance, inferInstance, hj,
    ⟨eP.trans (statedSLEquiv 3 _).symm⟩⟩

end ConfigRest

theorem ConfigRest.outer_of_alt47W
    {G : Type} [Group G] [Finite G] {L : Subgroup G} {c : G}
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) {P : Subgroup (L ⧸ aschbacherSolvableCore 3 L)}
    (h : ConfigRest (L ⧸ aschbacherSolvableCore 3 L) (Item426.thetaAut L hcN) P)
    (hout : ¬ IsInnerAut (Item426.thetaAut L hcN)) (halt : Alt47W L c)
    (hbig : ∃ N, 720 < N ∧ N ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ j : ℕ, 1 ≤ j ∧
      ((2 ^ (3 * j) % 3 = 1 ∧ OuterFieldSL (L ⧸ aschbacherSolvableCore 3 L) P j) ∨
        (2 ^ (3 * j) % 3 = 2 ∧ 2 ≤ j ∧ OuterFieldSU (L ⧸ aschbacherSolvableCore 3 L) P j)) := by
  have hX := h.quasisimple
  have hZ := h.center_ne_bot
  rcases halt with ⟨p, e, _, -, -, ⟨e1⟩, -⟩ |
      ⟨p, e, _, hp3, he1, he2, ⟨K, _, _, hSL⟩ | hIso, -⟩ |
      ⟨(⟨m, hm, ⟨⟨e1⟩⟩ | ⟨K, _, _, hKc, ⟨eK⟩⟩ | ⟨⟨e1⟩⟩ | ⟨K, _, _, hKc, ⟨eK⟩⟩⟩ |
        ⟨n, hn, hSz | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩ | hG2 | hF4⟩), -⟩ |
      ⟨n, hn, ⟨K, _, _, hSL⟩ | hIso, -⟩ | ⟨n, -, hD4⟩
  ·
    exact (false_of_projSL hX hZ e1).elim
  ·
    exfalso
    have hp : p.Prime := Fact.out
    rcases hSL with ⟨hKc, -, ⟨eK⟩⟩ | ⟨hKc, -, ⟨eK⟩⟩
    · obtain ⟨j, hj, -⟩ := h.outer_SL_card hout hp (by omega) hKc eK
      omega
    · have hU : UnitaryFieldData p e K := ⟨hp, he1, by rw [hKc, ← pow_mul, mul_comm]⟩
      have hq : 2 < p ^ e :=
        lt_of_lt_of_le (by omega : 2 < p) (Nat.le_self_pow (by omega) p)
      obtain ⟨h3e, -⟩ := h.outer_SU hout hU hq (by omega) eK
      omega
  ·
    rcases hIso with ⟨-, ⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩
    · exact (false_of_projSL hX hZ e1).elim
    · exact (false_of_projSU hX hZ le_rfl he1 e1).elim
  ·
    exact (false_of_projSL hX hZ e1).elim
  ·
    rcases Nat.lt_or_ge m 2 with hm1 | hm2
    · obtain rfl : m = 1 := by omega
      exact (false_of_mulEquiv_statedSU_three_two hX hKc eK).elim
    have hmod := mod_three_of_center_statedSU hm2 hKc eK h.three_dvd_card_center
    have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hKc, ← pow_mul, mul_comm]⟩
    have hq : 2 < 2 ^ m := by
      have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      omega
    obtain ⟨h3m, hr, K₀, _, h₀, ⟨eP⟩⟩ := h.outer_SU hout hU hq (by norm_num) eK
    obtain ⟨j, rfl⟩ := h3m
    have hj3 : 3 * j / 3 = j := by omega
    rw [hj3] at hr h₀ eP
    have hj2 : 2 ≤ j := by
      by_contra hj
      have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : Finite K₀ := h₀.finite
    refine ⟨j, by omega, Or.inr ⟨hmod, hj2, ⟨K, inferInstance, inferInstance, hKc, ⟨eK⟩⟩,
      K₀, inferInstance, inferInstance, by rw [h₀.card, ← pow_mul, mul_comm], ⟨eP⟩⟩⟩
  ·
    exact (false_of_projSU hX hZ le_rfl hm e1).elim
  ·
    obtain ⟨j, hj, K₀, _, _, hK₀, hP⟩ :=
      h.outer_SL_card hout Nat.prime_two (by norm_num) hKc eK
    refine ⟨j, by omega, Or.inl ⟨?_, ⟨K, inferInstance, inferInstance, ?_, ⟨eK⟩⟩,
      K₀, inferInstance, inferInstance, hK₀, hP⟩⟩
    · rw [hj]
      exact two_pow_two_mul_mod_three m
    · rw [hKc, hj]
  ·
    exact (false_of_suzuki hX hZ hSz).elim
  ·
    exact (false_of_projSL hX hZ e1).elim
  ·
    exact (false_of_projSp_two hX hZ hbig hn.pos e1).elim
  ·
    exact (false_of_chevalleyExceptional hX hZ (Or.inl rfl) hG2).elim
  ·
    exact (false_of_reeTits hX hZ (Or.inl rfl) hF4).elim
  ·
    rcases hSL with ⟨hKc, hmod, ⟨eK⟩⟩ | ⟨hKc, hmod, ⟨eK⟩⟩
    · obtain ⟨j, hj, K₀, _, _, hK₀, hP⟩ :=
        h.outer_SL_card hout Nat.prime_two (by norm_num) hKc eK
      subst hj
      exact ⟨j, by omega, Or.inl ⟨hmod, ⟨K, inferInstance, inferInstance, hKc, ⟨eK⟩⟩,
        K₀, inferInstance, inferInstance, hK₀, hP⟩⟩
    · rcases Nat.lt_or_ge n 2 with hn1 | hn2
      · obtain rfl : n = 1 := by omega
        exact (false_of_mulEquiv_statedSU_three_two hX hKc eK).elim
      have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hKc, ← pow_mul, mul_comm]⟩
      have hq : 2 < 2 ^ n := by
        have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
        omega
      obtain ⟨h3n, hr, K₀, _, h₀, ⟨eP⟩⟩ := h.outer_SU hout hU hq (by norm_num) eK
      obtain ⟨j, rfl⟩ := h3n
      have hj3 : 3 * j / 3 = j := by omega
      rw [hj3] at hr h₀ eP
      have hj2 : 2 ≤ j := by
        by_contra hj
        have : 2 ^ j ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have : Finite K₀ := h₀.finite
      exact ⟨j, by omega, Or.inr ⟨hmod, hj2, ⟨K, inferInstance, inferInstance, hKc, ⟨eK⟩⟩,
        K₀, inferInstance, inferInstance, by rw [h₀.card, ← pow_mul, mul_comm], ⟨eP⟩⟩⟩
  ·
    rcases hIso with ⟨-, ⟨e1⟩⟩ | ⟨-, ⟨e1⟩⟩
    · exact (false_of_projSL hX hZ e1).elim
    · exact (false_of_projSU hX hZ le_rfl hn e1).elim
  ·
    exact (false_of_chevalleyExceptional hX hZ (Or.inr rfl) hD4).elim

end CFSG.RankThree.PartTwo.Sec4.Item426Rest
