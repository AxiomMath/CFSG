module

public import CFSG.RankThree.PartOne.KC.UnitaryDefiningFour
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningLog
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIUnitarySocleBasic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.ComponentClassification.OutcomeLocal

namespace KCUnitaryDefining

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem npc_of_pow_eq_one {n : ℕ} (hp3 : 3 < p) (hn : n = 3 ∨ n = 4)
    (x : primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hxp : x ^ p = 1)
    (hx1 : x ≠ 1) : NormalPrimeComplementsTrivial p (MulAut.conj x) := by
  rcases hn with rfl | rfl
  · obtain ⟨N, hN, hskew, hN0, hx⟩ := exists_skew_log_of_pow_eq_one h (le_refl 3) (by omega) x hxp
      hx1
    rw [← hx]
    exact npc_three h hp3 hN hskew hN0
  · obtain ⟨N, hN, hskew, hN0, hx⟩ := exists_skew_log_of_pow_eq_one h (by norm_num) (by omega) x
      hxp hx1
    rw [← hx]
    exact npc_four h hp3 hN hskew hN0

end KCUnitaryDefining

theorem unitary_three_four_inner_defining_centralizer_local_cores_trivial {p f n : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData p f K) (hp3 : 3 < p) (hn : n = 3 ∨ n = 4)
    (B : Subgroup (MulAut (unitaryPSU h n)))
    (hB : (MulAut.conj : unitaryPSU h n →* MulAut (unitaryPSU h n)).range ≤ B)
    {a : MulAut (unitaryPSU h n)}
    (ha : a ∈ (MulAut.conj : unitaryPSU h n →* MulAut (unitaryPSU h n)).range)
    (hap : orderOf a = p) :
    (∀ S : Subgroup (MulAut (unitaryPSU h n)), S ≤ B ⊓ Subgroup.centralizer {a} →
      (S.subgroupOf (B ⊓ Subgroup.centralizer {a})).Normal → ¬ p ∣ Nat.card S → S = ⊥) ∧
    inSubgroup (aschbacherSolvableCore p) (B ⊓ Subgroup.centralizer {a}) = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite K := h.finite
  have hn3 : 3 ≤ n := by omega
  have hq := KCUnitaryDefining.not_three_and_pow_eq_two (n := n) h hp3
  set e := primeFormOneEquiv h n with he
  have : Finite (unitaryPSU h n) := Finite.of_equiv _ e.toEquiv
  have hinjP := KCUnitaryRegular.conj_injective_primeFormP h
    (KCUnitaryDefining.isPrimeFormGram_one (n := n) (K := K)) hn3 hq
  have hinjT : Function.Injective
      (MulAut.conj : unitaryPSU h n →* MulAut (unitaryPSU h n)) := by
    intro y₁ y₂ hy
    have h1 : MulAut.congr e.symm (MulAut.conj y₁) = MulAut.congr e.symm (MulAut.conj y₂) := by
      rw [hy]
    rw [KCUnitaryDefining.mulAutCongr_conj, KCUnitaryDefining.mulAutCongr_conj] at h1
    exact e.symm.injective (hinjP h1)
  obtain ⟨y, rfl⟩ := ha
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hap
    exact h.prime.one_lt.ne hap
  have hyp : y ^ p = 1 := by
    apply hinjT
    have h1 : (MulAut.conj y : MulAut (unitaryPSU h n)) ^ p = 1 := by
      have := pow_orderOf_eq_one (MulAut.conj y : MulAut (unitaryPSU h n))
      rwa [hap] at this
    rw [map_pow, map_one]
    exact h1
  have hxp : e.symm y ^ p = 1 := by rw [← map_pow, hyp, map_one]
  have hx1 : e.symm y ≠ 1 := fun hx => hy1 (by simpa using congrArg e hx)
  have hNPC : NormalPrimeComplementsTrivial p (MulAut.conj y) := by
    have h1 := (KCUnitaryDefining.npc_of_pow_eq_one h hp3 hn (e.symm y) hxp hx1).map_mulEquiv e
    rw [KCUnitaryDefining.mulAutCongr_conj, MulEquiv.apply_symm_apply] at h1
    exact h1
  exact ⟨fun S hSC hSn hSp => hNPC B hB S hSC hSn hSp,
    theta_centralizer_eq_bot_of_normalPrimeComplementsTrivial h.prime hNPC B hB⟩

end CFSG.RankThree.PartOne
