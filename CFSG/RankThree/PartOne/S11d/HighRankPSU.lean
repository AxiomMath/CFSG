module

public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11d.LowRank
public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.RankThree.PartOne.KF.ClsCover
public import CFSG.RankThree.PartOne.KF.ClsSUQuot
public import CFSG.RankThree.PartOne.KF.ClsSUUpper
public import CFSG.RankThree.PartOne.KF.R1Model
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PerfectCover CFSG.RankThree.PartOne.KFU CFSG.LocalAnalysis.ComponentInitial

theorem exists_prime_ge_five_dvd_two_pow_add_one {f : ℕ} (hf : 4 ≤ f) :
    ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ 2 ^ f + 1 := by
  by_contra hcon
  push Not at hcon
  have hne : 2 ^ f + 1 ≠ 0 := by positivity
  have hodd : Odd (2 ^ f + 1) := (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hall : ∀ {d : ℕ}, d.Prime → d ∣ 2 ^ f + 1 → d = 3 := by
    intro d hd hdvd
    have h5 := hcon d hd
    have hd2 : d ≠ 2 := by
      rintro rfl
      exact hodd.not_two_dvd_nat hdvd
    have hd5 : d < 5 := by
      by_contra hge
      exact absurd hdvd (h5 (by omega))
    interval_cases d <;> first | rfl | exact absurd hd (by decide) | omega
  have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hne hall
  have h80 : ∀ a : ℕ, 3 ^ a % 80 = 1 ∨ 3 ^ a % 80 = 3 ∨ 3 ^ a % 80 = 9 ∨ 3 ^ a % 80 = 27 := by
    intro a
    induction a with
    | zero => left; rfl
    | succ a ih => rw [pow_succ, Nat.mul_mod]; omega
  have h16 : 2 ^ f % 16 = 0 := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 4 := ⟨f - 4, by omega⟩
    rw [pow_add]
    norm_num
  have h5 : ¬ 5 ∣ 2 ^ f := by
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_five h)
    omega
  have hpos : 0 < 2 ^ f := by positivity
  have h := h80 (2 ^ f + 1).primeFactorsList.length
  rw [← hpow] at h
  omega

theorem card_hopfMultiplier_psu'
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {n f : ℕ} (hn : 6 ≤ n) (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    Group.IsPerfect (StatedProj (StatedSU n (2 ^ f) K)) ∧
      Nat.card (hopfMultiplier (StatedProj (StatedSU n (2 ^ f) K))) =
        Nat.gcd n (2 ^ f + 1) := by
  have hadm : StatedLieAdmissible .PSU n 2 f := by
    refine ⟨Nat.prime_two, by omega, by omega, ?_⟩
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  have hcl : StatedClassicalModel (StatedProj (StatedSU n (2 ^ f) K)) .PSU n 2 f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hm : Models.LieModel (StatedProj (StatedSU n (2 ^ f) K)) .PSU n 2 f :=
    ⟨hadm, Or.inl hcl⟩
  obtain ⟨hperf, hcard⟩ := card_hopfMultiplier_of_model hGA hm
  refine ⟨hperf, ?_⟩
  rw [hcard]
  have hgen : Blueprint.Multiplier.genericOrders .PSU n 2 f = (Nat.gcd n (2 ^ f + 1), 1) := rfl
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSU n 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp [Nat.card_prod, Nat.card_congr Multiplicative.toAdd]

theorem exists_cover_psu'
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {n f : ℕ} (hn : 6 ≤ n) (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) {L : Type} [Group L] [Finite L] (hLp : Group.IsPerfect L)
    (p : L →* StatedProj (StatedSU n (2 ^ f) K)) (hp : Function.Surjective p)
    (hpc : p.ker ≤ Subgroup.center L) :
    ∃ ρ : StatedSU n (2 ^ f) K →* L, Function.Surjective ρ ∧
      ρ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) := by
  obtain ⟨hperf, hcardM⟩ := card_hopfMultiplier_psu' hGA hn hf hK
  have hSU : Group.IsPerfect (StatedSU n (2 ^ f) K) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := f) hK (by omega) (by
      intro h
      simp only [Prod.mk.injEq] at h
      omega)
  set π : StatedSU n (2 ^ f) K →* StatedProj (StatedSU n (2 ^ f) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπk : π.ker = (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K) :=
    QuotientGroup.ker_mk' _
  have hπc : π.ker ≤ Subgroup.center (StatedSU n (2 ^ f) K) := by
    rw [hπk]
    exact CFSG.RankThree.PartTwo.Census.statedScalars_subgroupOf_le_center _
  have hcard : Nat.card (hopfMultiplier (StatedProj (StatedSU n (2 ^ f) K))) =
      Nat.card π.ker := by
    rw [hcardM, hπk, (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by omega)).2.2]
  obtain ⟨ρ, hρ, hρs⟩ := exists_hom_of_card_multiplier_eq hperf hSU π hπs hπc hcard p hp hpc
  refine ⟨ρ, hρs hLp, fun x hx => ?_⟩
  have h1 : π x = 1 := by
    rw [← hρ, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one]
  rw [← hπk]
  exact h1

theorem TCX.highRankFalse_PSU : TCX.HighRankFalse .PSU := by
  intro hGA J _ _ p n f₀ hq hp hp5 hf₀ hZ2 hZ he hM hnl
  have hn6 : 6 ≤ n := by
    simp only [TCX.LowRank, not_le] at hnl
    omega
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ :=
    (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp hM
  have hf5 : 5 ≤ p * f₀ := by nlinarith
  have hf1 : 1 ≤ p * f₀ := by omega
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center J)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hZ
  have hqq := isCentralPQuot_center e hcop
  obtain ⟨ρ, hρs, hρk⟩ := exists_cover_psu' hGA hn6 (by omega) hK hq.1 _ hqq.surjective hqq.central
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := p * f₀ * 2)
      (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul])
  have hU : UnitaryFieldData 2 (p * f₀) K := unitaryFieldData_two hK hf1
  have hr : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ (p * f₀) + 1 ∧ (6 < n ∨ ¬ r ∣ n) := by
    by_cases h7 : 7 ≤ n
    · obtain ⟨r, hr, hr2, hrq⟩ :=
        CFSG.RankThree.PartTwo.Census.exists_odd_prime_dvd_two_pow_add_one hf1
      exact ⟨r, hr, hr2, hrq, Or.inl (by omega)⟩
    · obtain ⟨r, hr, hr5, hrq⟩ := exists_prime_ge_five_dvd_two_pow_add_one (by omega : 4 ≤ p * f₀)
      refine ⟨r, hr, by omega, hrq, Or.inr ?_⟩
      have hn : n = 6 := by omega
      subst hn
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases r <;> first | omega | exact absurd hr (by decide)
  obtain ⟨r, hr, hr2, hrq, hcen⟩ := hr
  have h4 := CFSG.RankThree.PartOne.KFU.le_localRank_of_surjective_statedSU_torus (k := 3) hU hr
    hrq (by omega) (hcen.imp_left fun h => by omega) ρ hρs hρk
  have h3 := (CFSG.RankThree.OddKernel.localRank_le_evenRank hr hr2).trans he
  omega

end CFSG.RankThree.PartOne
