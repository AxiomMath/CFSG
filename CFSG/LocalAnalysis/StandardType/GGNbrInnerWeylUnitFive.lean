module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylScIrred
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreU
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHyperbolic
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag

theorem ggSCNoLine_of_scWeylIrred {p r : ℕ} {R : Type} [Group R] (hp : p.Prime)
    (h : GGSCWeylIrred p r R) : GGSCNoLine p r R := by
  intro E hE hr h3 hsc e he he1
  by_contra hcon
  push Not at hcon
  have hEle : Subgroup.zpowers e ≤ E := Subgroup.zpowers_le.mpr he
  rcases h E hE hr h3 hsc (Subgroup.zpowers e) hEle (fun g hg x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ (hcon g hg) k) with h0 | hE'
  · exact he1 (Subgroup.zpowers_eq_bot.mp h0)
  · have := Fact.mk hp
    have hcard : Nat.card E = p := by
      rw [← hE', Nat.card_zpowers]
      exact orderOf_eq_prime (hE.2 e he) he1
    have h1 : p ^ 3 ≤ p := hcard ▸ h3
    have h2 : p < p ^ 3 :=
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact absurd h1 (not_le.mpr h2)

theorem ggNbrCenter_eq_bot_of_simple_of_exists_noncomm {R : Type} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    exfalso
    apply hab
    have ha : a ∈ Subgroup.center R := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.mp ha b).symm

section Cover


theorem ggCenterPrime_psu_unitary {n d p : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hd : 5 ≤ d) (hd6 : (d, n) ≠ (6, 1)) (hp : p.Prime)
    (hpq : ¬ p ∣ 2 ^ n + 1)
    (hZ : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) = ⊥) :
    GGCenterPrime p (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
  classical
  intro L' _ _ ψ hψ hker hperf hdvd
  have := Fact.mk hp
  obtain ⟨-, hcov⟩ := LineU.unitaryCoverAt hK hd hd6
  obtain ⟨φ, hφ⟩ := hcov L' ψ hψ hker hperf
  have hφs : Function.Surjective φ :=
    LineU.surjective_of_cover (LargeEvenProjMk (unitarySU 2 n K d))
      (QuotientGroup.mk'_surjective _) ψ hker hperf φ hφ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzc : (z : L') ∈ Subgroup.center L' := z.2
  have hψz : ψ (z : L') = 1 := by
    have hmem : ψ (z : L') ∈
        Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l', rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzc l']
    rw [hZ] at hmem
    exact Subgroup.mem_bot.mp hmem
  obtain ⟨s, hs⟩ := hφs (z : L')
  have hs1 : LargeEvenProjMk (unitarySU 2 n K d) s = 1 := by
    have h1 := hφ s
    rw [hs] at h1
    exact h1.symm.trans hψz
  have h2 : s ∈ (LargeEvenScalars (Fin d) K).subgroupOf (unitarySU 2 n K d) :=
    (QuotientGroup.eq_one_iff s).mp hs1
  rw [Subgroup.mem_subgroupOf, largeEvenScalars_def] at h2
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp h2
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin d) c ∈ CFSG.Open.StatedSU d (2 ^ n) K := by
    rw [hc]
    exact s.2
  have hcq : c ^ (2 ^ n + 1) = 1 :=
    ((CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two hK (by omega) c).mp hmem).2
  have hsq : s ^ (2 ^ n + 1) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hcq, map_one]
    rfl
  have hl : (z : L') ^ (2 ^ n + 1) = 1 := by rw [← hs, ← map_pow, hsq, map_one]
  apply hpq
  have hord : orderOf (z : L') = p := by rw [Subgroup.orderOf_coe]; exact hz
  rw [← hord]
  exact orderOf_dvd_of_pow_eq_one hl

theorem largeEvenLabelAll_noLine_unitFive {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twA ∧ lab.rank = 5 ∧ p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∃ r, (GGTorusLift p r R ∨ r = 0) ∧ GGTorusNoLine p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hpq⟩ := h
  dsimp only at ht hl hpq ⊢
  subst ht hl
  have hn : 1 ≤ n := hlab.1
  have hq4 : 4 ≤ 2 ^ n := four_le_two_pow_of_dvd_sub_one hp hp2 hn hpq
  have hpq' : ¬ p ∣ 2 ^ n + 1 := not_dvd_two_pow_add_one_of_dvd_sub_one hp hp2 hpq
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  refine ⟨K, i1, i2, hK, hQ', fun hs hna => ⟨0, Or.inr rfl, ?_⟩⟩
  have hZ := ggNbrCenter_eq_bot_of_simple_of_exists_noncomm hs hna
  have hd6 : ((5 + 1 : ℕ), n) ≠ (6, 1) := fun he => by
    have h1 : n = 1 := congrArg Prod.snd he
    subst h1
    omega
  exact ggTorusNoLine_of_scNoLine hp hZ
    (NbrInnerMore.ggOutdiagPrime_unitary_of_not_dvd hK hn (by omega) (by omega) hp hpq')
    (ggCenterPrime_psu_unitary hK (by omega) hd6 hp hpq' hZ)
    (ggSCNoLine_of_scWeylIrred hp
      (ggSCWeylIrred_statedProj_hyp hK hn hp hp2 hpq (r := 3) (Or.inr rfl)))

end Cover

section Main

theorem ggNbrInnerWeylOn_unitFive : GGNbrInnerWeylOn GGNbrWeylUnitFiveLabel :=
  ggNbrInnerWeylOn_of_labels fun p lab hp hp2 hlab ⟨hpow, ht, hl, hpq⟩ =>
    largeEvenLabelAll_weylInnerKLevel_of_noLine_or
      (largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow)
      (largeEvenLabelAll_noLine_unitFive hp hp2 hlab ⟨ht, hl, hpq⟩)

end Main

end CFSG.StandardType

end
