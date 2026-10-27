module

public import CFSG.RankThree.GroupTheory.ThetaComponents
import CFSG.LocalAnalysis.ComponentClassification.RadicalFreeLayer
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open scoped commutatorElement

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

theorem open_isQuasisimple_of {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

theorem pow_orderOf_three_of_quotient {K : Type*} [Group K] [Finite K] {N : Subgroup K} [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {y : K} (hy : orderOf (y : K ⧸ N) = 3) :
    ∃ k : ℕ, orderOf (y ^ k) = 3 ∧ ((y ^ k : K) : K ⧸ N) = (y : K ⧸ N) := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have hdvd : 3 ∣ orderOf y := by
    rw [← hy]
    exact orderOf_map_dvd (QuotientGroup.mk' N) y
  obtain ⟨a, m, hm, hn⟩ : ∃ a m : ℕ, ¬ 3 ∣ m ∧ orderOf y = 3 ^ a * m :=
    ⟨(orderOf y).factorization 3, orderOf y / 3 ^ (orderOf y).factorization 3,
      Nat.not_dvd_ordCompl h3 (orderOf_pos y).ne',
      (Nat.ordProj_mul_ordCompl_eq_self (orderOf y) 3).symm⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
    rw [h, mul_zero] at hn
    exact (orderOf_pos y).ne' hn
  set u := y ^ m with hu
  have hmdvd : m ∣ orderOf y := ⟨3 ^ a, by rw [hn, mul_comm]⟩
  have hou : orderOf u = 3 ^ a := by
    rw [hu, orderOf_pow_of_dvd hm0.ne' hmdvd, hn, Nat.mul_div_cancel _ hm0]
  have hcop : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd h3).mpr hm
  have houbar : orderOf (u : K ⧸ N) = 3 := by
    rw [hu, QuotientGroup.mk_pow, Nat.Coprime.orderOf_pow (by rw [hy]; exact hcop), hy]
  have hu3N : u ^ 3 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← houbar, pow_orderOf_eq_one]
  have hu3 : u ^ 3 = 1 := by
    have hpow : (u ^ 3) ^ 3 ^ a = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← hou, pow_orderOf_eq_one, one_pow]
    have hord : orderOf (u ^ 3) ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one hpow
    have hordN : orderOf (⟨u ^ 3, hu3N⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hordN
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow h3).mp hord
    rcases b with _ | b
    · rwa [pow_zero, orderOf_eq_one_iff] at hb
    · exact absurd ((dvd_pow_self 3 (Nat.succ_ne_zero b)).trans (hb ▸ hordN)) hN
  have hu1 : u ≠ 1 := fun h => by
    rw [h, QuotientGroup.mk_one, orderOf_one] at houbar
    norm_num at houbar
  have hou3 : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hm3 : m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hybar3 : (y : K ⧸ N) ^ 3 = 1 := by rw [← hy, pow_orderOf_eq_one]
  rcases hm3 with h1 | h2
  · refine ⟨m, hou3, ?_⟩
    rw [QuotientGroup.mk_pow, ← Nat.div_add_mod m 3, h1, pow_add, pow_mul, hybar3, one_pow,
      one_mul, pow_one]
  · refine ⟨2 * m, ?_, ?_⟩
    · rw [mul_comm, pow_mul, ← hu, Nat.Coprime.orderOf_pow (by rw [hou3]; norm_num), hou3]
    · rw [QuotientGroup.mk_pow]
      have : 2 * m = 3 * (2 * (m / 3) + 1) + 1 := by omega
      rw [this, pow_add, pow_mul, hybar3, one_pow, one_mul, pow_one]

theorem aschbacherSolvableCore_eq_pPrimeCore_of_forall {X : Type*} [Group X] [Finite X]
    (h : ∀ J ∈ thetaComponents 3 X, 3 ∣ Nat.card J) :
    aschbacherSolvableCore 3 X = CFSG.pPrimeCore 3 X := by
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  obtain ⟨-, hθc, hθ3, -, -⟩ := solvable_prime_complement_core_characterization (H := X) h3
  set θ := aschbacherSolvableCore 3 X with hθdef
  have : θ.Normal := @Subgroup.normal_of_characteristic _ _ θ hθc
  have hNn : (CFSG.pPrimeCore 3 X).Normal := CFSG.pPrimeCore_normal (p := 3) (G := X)
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 X) :=
    (Nat.Prime.coprime_iff_not_dvd h3).mp (CFSG.pPrimeCore_coprime_card (p := 3) (G := X))
  refine le_antisymm
    (le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd h3).mpr hθ3⟩) ?_
  by_contra hle
  set π := QuotientGroup.mk' θ with hπ
  set M := (CFSG.pPrimeCore 3 X).map π with hMdef
  have hMn : M.Normal := hNn.map π (QuotientGroup.mk'_surjective θ)
  have hM3 : ¬ 3 ∣ Nat.card M := fun hd =>
    hN3 (hd.trans (Subgroup.card_map_dvd (CFSG.pPrimeCore 3 X) π))
  have hM1 : M ≠ ⊥ := by
    intro hM
    apply hle
    intro x hx
    have hx' : π x = 1 := by
      have : π x ∈ M := Subgroup.mem_map_of_mem π hx
      rwa [hM, Subgroup.mem_bot] at this
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
  have hθq : aschbacherSolvableCore 3 (X ⧸ θ) = ⊥ := theta_quotient_core_and_ranks.1
  have hfree : ComponentClassification.SolvableRadical.Free M := by
    rw [ComponentClassification.SolvableRadical.free_iff_eq_bot]
    set R := ComponentClassification.SolvableRadical.subgroup M with hRdef
    have : R.Characteristic := ComponentClassification.SolvableRadical.characteristic M
    have hRs : Group.IsSolvable R := ComponentClassification.SolvableRadical.solvable M
    set R' := R.map M.subtype with hR'def
    have hR'n : R'.Normal := ConjAct.normal_of_characteristic_of_normal
    have hR's : Group.IsSolvable R' :=
      Group.isSolvable_of_surjective (f := (R.equivMapOfInjective M.subtype
        M.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
    have hR'3 : ¬ 3 ∣ Nat.card R' := fun hd => by
      apply hM3
      rw [hR'def, Subgroup.card_map_of_injective M.subtype_injective] at hd
      exact hd.trans (Subgroup.card_subgroup_dvd_card R)
    have hR'le : R' ≤ aschbacherSolvableCore 3 (X ⧸ θ) :=
      (solvable_prime_complement_core_characterization (H := X ⧸ θ) h3).2.2.2.1 R' hR'n hR's
        hR'3
    rw [hθq, le_bot_iff, hR'def, Subgroup.map_eq_bot_iff_of_injective _
      M.subtype_injective] at hR'le
    exact hR'le
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).mpr hM1
  obtain ⟨K, -, hKsub, hKq⟩ := ComponentClassification.RadicalFreeLayer.exists_component hfree
  set K' := K.map M.subtype with hK'def
  have hK'comp : IsComponent K' := by
    refine ⟨LocalCores.isQuasisimple_of_mulEquiv (K.equivMapOfInjective M.subtype
      M.subtype_injective) (isQuasisimple_of_open hKq), ?_⟩
    have hKsn : K.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hKsub
    exact hKsn.trans' (Subgroup.Normal.isSubnormal hMn)
  obtain ⟨hJ, hJmap⟩ := perfectResidual_comap_mem_thetaComponents h3 hK'comp
  set J := inSubgroup perfectResidual (K'.comap π) with hJdef
  have hJ3 := h J hJ
  obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map h3 hJ.2.1
  have hθJ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 J) :=
    (solvable_prime_complement_core_characterization (H := J) h3).2.2.1
  have hcardJ : Nat.card J =
      Nat.card (aschbacherSolvableCore 3 J) * Nat.card (J ⧸ aschbacherSolvableCore 3 J) := by
    rw [mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hK'3 : 3 ∣ Nat.card K' := by
    rw [← hJmap, ← Nat.card_congr η.toEquiv]
    rw [hcardJ] at hJ3
    exact (Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.Prime.coprime_iff_not_dvd h3).mpr hθJ3) hJ3)
  apply hM3
  rw [hK'def, Subgroup.card_map_of_injective M.subtype_injective] at hK'3
  exact hK'3.trans (Subgroup.card_subgroup_dvd_card K)

end CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB
