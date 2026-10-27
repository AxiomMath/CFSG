module

public import CFSG.LocalAnalysis.UniquenessCase.UCKPFI1
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.SeitzReduction.RankOneU3StarLocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.BenderSuzuki
  CFSG.BenderSuzuki.MatrixGroups
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem prime_dvd_torus_card {Q q : ℕ} (hq : q.Prime) (hq3 : 3 < q) (hqf : q ∣ Q + 1) (hQ : 1 ≤ Q) :
    q ∣ (Q ^ 2 - 1) / Nat.gcd 3 (Q + 1) := by
  have hfactor : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq Q 1
  have hd : Nat.gcd 3 (Q + 1) ∣ Q ^ 2 - 1 := by
    rw [hfactor]
    exact Dvd.dvd.mul_left (Nat.gcd_dvd_right 3 (Q + 1)) _
  have hqN : q ∣ Q ^ 2 - 1 := by
    rw [hfactor]
    exact Dvd.dvd.mul_left hqf _
  have hcop : Nat.Coprime q (Nat.gcd 3 (Q + 1)) := by
    refine Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 (Q + 1)) ?_
    refine (Nat.Prime.coprime_iff_not_dvd hq).2 fun h => ?_
    have := Nat.le_of_dvd (by norm_num) h
    omega
  obtain ⟨m, hm⟩ := hd
  have hpos : 0 < Nat.gcd 3 (Q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rw [hm, Nat.mul_div_cancel_left _ hpos]
  rw [hm] at hqN
  exact hcop.dvd_of_dvd_mul_left hqN

theorem cube_add_one_mod {Q r : ℕ} (hr3 : 3 ≤ r) (hQ : Q % r = 1) : (Q ^ 3 + 1) % r = 2 := by
  have h1 : Q ^ 3 % r = 1 := by
    rw [Nat.pow_mod, hQ]
    simp [Nat.one_mod_eq_one.2 (by omega : r ≠ 1)]
  rw [Nat.add_mod, h1, Nat.one_mod_eq_one.2 (by omega : r ≠ 1)]
  exact Nat.mod_eq_of_lt (by omega)

theorem fixed_inner_psu_model {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2) (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {r : ℕ} (hr : r.Prime) (hr3 : 3 ≤ r)
    (hrq : 2 ^ f % r = 1) {s : ProjectiveSpecialUnitaryMatrixGroup J} (hs : s ^ r = 1) {q : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) (hqf : q ∣ 2 ^ f + 1) :
    ∃ z : ProjectiveSpecialUnitaryMatrixGroup J, orderOf z = q ∧ z * s = s * z := by
  classical
  have h := unitary_three_point_structure J f hf hcard hfixed hJ
  obtain ⟨-, -, -, -, -, rho, -, -, hΩ, h2, hstabα, hstabβ, -, -, -, hTeq, hTcyc, hTcard, -⟩ := h
  have hβα : unitaryOuterIsotropicPoint J hJ 2 (by decide) ≠ unitaryOuterIsotropicPoint J hJ 0 (by decide) :=
    fun h => unitaryCoordinatePoint_two_ne_zero (congrArg Subtype.val h)
  have hfin : Finite (unitaryIsotropicPoints J) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hΩ]
    exact Nat.succ_ne_zero _
  have hT : ∀ g : ProjectiveSpecialUnitaryMatrixGroup J,
      rho g (unitaryOuterIsotropicPoint J hJ 0 (by decide)) = unitaryOuterIsotropicPoint J hJ 0 (by decide) →
      rho g (unitaryOuterIsotropicPoint J hJ 2 (by decide)) = unitaryOuterIsotropicPoint J hJ 2 (by decide) →
      g ∈ (torusPSU J hJ).range := by
    intro g h1 h2
    rw [hTeq]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [← hstabα]
      exact MulAction.mem_stabilizer_iff.2 h1
    · rw [← hstabβ]
      exact MulAction.mem_stabilizer_iff.2 h2
  have hTc : ∀ x ∈ (torusPSU J hJ).range, ∀ y ∈ (torusPSU J hJ).range, x * y = y * x := by
    obtain ⟨g, hg⟩ := hTcyc.exists_zpow_surjective
    intro x hx y hy
    obtain ⟨a, ha⟩ := hg ⟨x, hx⟩
    obtain ⟨b, hb⟩ := hg ⟨y, hy⟩
    have hab : (⟨x, hx⟩ : (torusPSU J hJ).range) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      rw [← ha, ← hb, ← zpow_add, ← zpow_add, add_comm]
    exact congrArg Subtype.val hab
  have hΩmod : Nat.card (unitaryIsotropicPoints J) % r = 2 := by
    rw [hΩ]
    exact cube_add_one_mod hr3 hrq
  have hqT : q ∣ Nat.card (torusPSU J hJ).range := by
    rw [hTcard]
    exact prime_dvd_torus_card hq hq3 hqf Nat.one_le_two_pow
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' q hqT
  obtain ⟨g, hg⟩ := exists_conj_commute_of_fixed_points rho h2 hβα.symm hT hTc hr hr3 hΩmod hs
    (z₀ := (z₀ : ProjectiveSpecialUnitaryMatrixGroup J)) z₀.2
  refine ⟨g * (z₀ : ProjectiveSpecialUnitaryMatrixGroup J) * g⁻¹, ?_, hg⟩
  rw [orderOf_conj_fi, Subgroup.orderOf_coe, hz₀]

theorem fixed_inner_of_isU3 {Y : Type} [Group Y] {n : ℕ} (hn : 2 ≤ n) (hY : IsU3 Y n) {r : ℕ}
    (hr : r.Prime) (hr3 : 3 ≤ r) (hrq : 2 ^ n % r = 1) {s : Y} (hs : s ^ r = 1) {q : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) (hqn : q ∣ 2 ^ n + 1) :
    ∃ z : Y, orderOf z = q ∧ z * s = s * z := by
  obtain ⟨E, _, _, J, hJ, hcard, hfixed, ⟨e₂⟩⟩ := CFSG.GH74.Uniqueness.Bender.exists_psu3_concrete hn
  obtain ⟨e₁⟩ := CFSG.ComponentClassification.GMS78.nonempty_mulEquiv_psu3_of_stated hn
    (CFSG.SeitzReduction.RankOne.statedClassicalModel_of_lieModel_psu3 hY)
  have hmodel : PSU3Model n = CFSG.Open.PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
  let φ : Y ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
    (e₁.trans (MulEquiv.subgroupCongr hmodel.symm)).trans e₂
  obtain ⟨z, hz, hzs⟩ := fixed_inner_psu_model J n hn hcard hfixed hJ hr hr3 hrq
    (s := φ s) (by rw [← map_pow, hs, map_one]) hq hq3 hqn
  refine ⟨φ.symm z, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hz
  · have : φ.symm z * φ.symm (φ s) = φ.symm (φ s) * φ.symm z := by
      rw [← map_mul, ← map_mul, hzs]
    simpa using this

end CFSG.LocalAnalysis.UniquenessCase.UCK
