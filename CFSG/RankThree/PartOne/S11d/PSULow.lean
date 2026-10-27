module

public import CFSG.RankThree.PartOne.KF.F128SU
public import CFSG.RankThree.PartOne.K128.FixCenter
public import CFSG.RankThree.PartOne.S11d.FixedFactsPSU
public import CFSG.RankThree.PartOne.S11d.LowRank
import CFSG.RankThree.PartOne.K128.SylowShapeRank

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.KFU
open CFSG.RankThree.PartOne.K1214 (SylowShape)
open CFSG.RankThree.PartOne.K128 (zmodIncl zmodIncl_injective)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.Blueprint (LieModel)

theorem two_le_pRank_of_sylowShape' {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) {X : Type*} [Group X]
    [Finite X] (h : SylowShape p 2 e X) : 2 ≤ CFSG.pRank p X :=
  CFSG.RankThree.PartOne.K1214.two_le_pRank_of_sylowShape_sq hp he h

theorem psu_low_cases {T : Type} [Group T] [Finite T] {p n f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hLR2 : LocalRankLeTwo p T) (h2 : 2 ≤ CFSG.pRank p T) (hf₀ : 1 ≤ f₀)
    (hM : LieModel T .PSU n 2 (p * f₀)) (hn5 : n ≤ 5) (α : MulAut T) (hαp : α ^ p = 1)
    (hαinn : α ∉ innerAut T) (hLRA : LocalRankAut p T α) :
    n = 3 ∧ p ∣ 2 ^ (p * f₀) + 1 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  have hf1 : 1 ≤ p * f₀ := by omega
  have hcl : StatedClassicalModel T .PSU n 2 (p * f₀) :=
    K1214.statedClassicalModel_of_lieModel_of_tag' (Or.inl rfl) hM
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := id hcl
  have hn3 : 3 ≤ n := hadm.2.2.1
  have : CharP K 2 := K128.charP_two_of_card_eq_two_pow (f := p * f₀ * 2) (by rw [hK, ← pow_mul])
  have hU : UnitaryFieldData 2 (p * f₀) K := unitaryFieldData_two hK hf1
  have hq32 : 2 ^ 5 ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) hf5
  have hT0 : Subgroup.center T = ⊥ := by
    have hSU : Group.IsPerfect (StatedSU n (2 ^ (p * f₀)) K) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := p * f₀) hK hn3 (by
        intro h
        simp only [Prod.mk.injEq] at h
        omega)
    exact center_eq_bot_of_cover hSU
      (e.symm.toMonoidHom.comp (QuotientGroup.mk' _)) (e.symm.surjective.comp
        (QuotientGroup.mk'_surjective _)) hcl
  have hpQ : ¬ p ∣ 2 ^ (p * f₀) := fun h => hp2
    ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
  have hlr : ∀ r : ℕ, r.Prime →
      localRank r T = localRank r (StatedProj (StatedSU n (2 ^ (p * f₀)) K)) :=
    fun r hr => CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hr
  have hrank1 : ¬ p ∣ 2 ^ (p * f₀) + 1 → n / orderOf (-((2 ^ (p * f₀) : ℕ) : ZMod p)) ≤ 1 →
      CFSG.pRank p T ≤ 1 := by
    intro hpq' h
    have hN : ¬ p ∣ Nat.card
        ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ (p * f₀)) K)) := by
      rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by omega)).2.2]
      exact fun hd => hpq' (hd.trans (Nat.gcd_dvd_right _ _))
    rw [pRank_eq_of_mulEquiv_of_one_lt hp.one_lt e]
    rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _ hN]
    exact pRank_statedSU_le_one hp hp2 hK hpQ (by omega) h
  have hq1 : 1 ≤ 2 ^ (p * f₀) := Nat.one_le_two_pow
  by_cases hpq' : p ∣ 2 ^ (p * f₀) + 1
  ·
    have hpg : p ∣ 2 ^ f₀ + 1 := dvd_two_pow_add_one_of_mul hp hpq'
    obtain ⟨e', m, m', he2, hm', hm'p, hmm, hmp⟩ := K1214.lte_plus hp hp2 hpg
    interval_cases n
    · exact ⟨rfl, hpq'⟩
    ·
      exfalso
      exact false_of_row kf122Row9_holds hp hp5 hT0
        ⟨p * f₀, hf1, hpq', statedClassicalModel_congr (topQuotEquiv hT0) hcl⟩ hLR2 hαp hαinn hLRA
    ·
      exfalso
      have h3 : 3 ≤ localRank p (StatedProj (StatedSU 5 (2 ^ (p * f₀)) K)) := by
        by_cases hp5' : p = 5
        · subst hp5'
          have hp25 : 5 ^ 2 ∣ 2 ^ (5 * f₀) + 1 := by
            refine ⟨5 ^ (e' - 2) * m, ?_⟩
            rw [hmm, ← mul_assoc, ← pow_add]
            congr 2
            omega
          exact le_localRank_statedSU_lift hU hp hp2 hp25 (dvd_refl 5) (by norm_num) (by norm_num)
        · refine CFSG.RankThree.PartTwo.Census.le_localRank_statedSU_torus (k := 2) hU hp hpq'
            (by norm_num) (Or.inr ?_)
          exact fun hd => hp5' ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hd)
      rw [← hlr p hp] at h3
      exact false_of_three_le_localRank hp hLR2 h3
  · by_cases hpq : p ∣ 2 ^ (p * f₀) - 1
    ·
      exfalso
      interval_cases n
      ·
        have hd2 := two_le_orderOf_neg_of_not_dvd hp hpQ hpq'
        have := hrank1 hpq' ((Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega))))
        omega
      · exact false_of_row kf122Row5_holds hp hp5 hT0
          ⟨p * f₀, hf1, hpq, statedClassicalModel_congr (topQuotEquiv hT0) hcl⟩ hLR2 hαp hαinn hLRA
      · exact false_of_row kf122Row6_holds hp hp5 hT0
          ⟨p * f₀, hf1, hpq, statedClassicalModel_congr (topQuotEquiv hT0) hcl⟩ hLR2 hαp hαinn hLRA
    ·
      exfalso
      have hd3 := three_le_orderOf_neg_of_not_dvd hp hpQ hpq hpq' hq1
      have := hrank1 hpq' (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega)))
      omega

theorem TCX.fixedRankTL_PSU : TCX.FixedRankTL .PSU := by
  intro T _ _ p hp hp5 hLR2 h2 n f₀ hf₀ hM hlow α hαp hαinn hLRA hX
  obtain ⟨rfl, hpQ⟩ := psu_low_cases hp hp5 hLR2 h2 hf₀ hM hlow α hαp hαinn hLRA
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  have hF : FixedFacts p α := tagFixedFacts_PSU T p hp hp5 hLR2 3 f₀ hf₀ hM α hαp hαinn hLRA hX α
    hαp hαinn hLRA ⟨1, fun h => by
      have := Int.eq_one_of_dvd_one (by positivity) h
      omega, by
      rw [zpow_one, mul_inv_cancel]
      exact (innerAut T).one_mem⟩
  have hXc : Blueprint.LieModel (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) .PSU 3 2 f₀ := by
    rcases hX with hX | ⟨ht, -⟩
    · exact hX
    · exact absurd ht (by decide)
  have hclN := K1214.statedClassicalModel_of_lieModel_of_tag' (Or.inl rfl) hXc
  have hpg : p ∣ 2 ^ f₀ + 1 := dvd_two_pow_add_one_of_mul hp hpQ
  obtain ⟨e', m, m', he2, hm', hm'p, -, -⟩ := K1214.lte_plus hp hp2 hpg
  have hsh : SylowShape p 2 (e' - 1) (↥(fixRes α) ⧸ Subgroup.center ↥(fixRes α)) :=
    K1214.sylowShape_of_psu3Model hp hp2 hp3 (by omega) hm' hm'p hclN
  exact two_le_pRank_of_sylowShape' hp (by omega)
    (SylowShape.of_mulEquiv (K128.fixResEquivQuotient hF) hsh)

end CFSG.RankThree.PartOne
