module

public import CFSG.ClassicalGroups.UnitaryFlag.SU3TorusFrame
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3EvenCentPerfectSU
import CFSG.GroupTheory.PerfectSylowInversion
import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThreeSU
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3TorusIrred

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open scoped Pointwise

variable {n : ℕ} {K : Type} [Field K] {T H : Subgroup (unitarySU 2 n K 3)}

private lemma three_dvd_of_mul_eq {a b c d : ℕ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (h : c * d = a * b)
    (ha : 3 ∣ a) (hc : padicValNat 3 c ≤ padicValNat 3 b) : 3 ∣ d := by
  have hab : 0 < a * b := Nat.mul_pos (Nat.pos_of_ne_zero ha0) (Nat.pos_of_ne_zero hb0)
  have hcd : c * d ≠ 0 := by rw [h]; exact hab.ne'
  have hc0 : c ≠ 0 := left_ne_zero_of_mul hcd
  have hd0 : d ≠ 0 := right_ne_zero_of_mul hcd
  have hv : padicValNat 3 c + padicValNat 3 d = padicValNat 3 a + padicValNat 3 b := by
    rw [← padicValNat.mul hc0 hd0, h, padicValNat.mul ha0 hb0]
  have h1 : 1 ≤ padicValNat 3 a := one_le_padicValNat_of_dvd ha0 ha
  have hd : 0 < padicValNat 3 d := by omega
  exact (dvd_iff_padicValNat_ne_zero hd0).mpr hd.ne'

private lemma padicValNat_three_card_statedSU (n : ℕ) (h3q : 3 ∣ 2 ^ n - 1) (hn : 1 ≤ n) :
    padicValNat 3 ((2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1)) =
      padicValNat 3 (2 ^ n - 1) := by
  set q := 2 ^ n
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ q := Nat.pow_le_pow_right (by norm_num) hn
  have hq1 : 1 ≤ q := by omega
  have hq0 : q ≠ 0 := by omega
  have hqsub0 : q - 1 ≠ 0 := by omega
  have hqadd0 : q + 1 ≠ 0 := by omega
  have hq2sub0 : q ^ 2 - 1 ≠ 0 := by
    have : 1 < q ^ 2 := by nlinarith
    omega
  have hq3add0 : q ^ 3 + 1 ≠ 0 := by
    have : 0 < q ^ 3 := pow_pos (by omega) 3
    omega
  have hq2q1 : q ^ 2 - q + 1 ≠ 0 := by
    have : q ≤ q ^ 2 := by nlinarith
    omega
  have h3q' : 3 ∣ q - 1 := by
    simpa [q] using h3q
  have h3qadd : ¬ 3 ∣ q + 1 := by
    intro h
    have h2 : 3 ∣ (q + 1) - (q - 1) := Nat.dvd_sub h h3q'
    rw [show q + 1 - (q - 1) = 2 by omega] at h2
    omega
  have h3q2q1 : ¬ 3 ∣ q ^ 2 - q + 1 := by
    have hq2q : q ^ 2 - q = q * (q - 1) := by
      have hqq : q ≤ q ^ 2 := by nlinarith
      zify [hq1, hqq]
      ring
    have h3q2q : 3 ∣ q ^ 2 - q := by rw [hq2q]; exact dvd_mul_of_dvd_right h3q' q
    intro h
    have h1 : 3 ∣ (q ^ 2 - q + 1) - (q ^ 2 - q) := Nat.dvd_sub h h3q2q
    rw [show q ^ 2 - q + 1 - (q ^ 2 - q) = 1 by omega] at h1
    omega
  have hq3 : padicValNat 3 (q ^ 3) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have h2 : 3 ∣ q := Nat.prime_three.dvd_of_dvd_pow h
    exact (by omega : ¬ 3 ∣ q) h2
  have hfac1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    have hqq : 1 ≤ q ^ 2 := by nlinarith
    zify [hq1, hqq]
    ring
  have hfac2 : q ^ 3 + 1 = (q + 1) * (q ^ 2 - q + 1) := by
    have hqq : q ≤ q ^ 2 := by nlinarith
    zify [hq1, hqq]
    ring
  have hq21 : padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q - 1) + padicValNat 3 (q + 1) := by
    rw [hfac1, padicValNat.mul hqsub0 hqadd0]
  have hq31 : padicValNat 3 (q ^ 3 + 1) =
      padicValNat 3 (q + 1) + padicValNat 3 (q ^ 2 - q + 1) := by
    rw [hfac2, padicValNat.mul hqadd0 hq2q1]
  have hK : padicValNat 3 (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1))
      = padicValNat 3 (q ^ 3) + padicValNat 3 (q ^ 2 - 1) + padicValNat 3 (q ^ 3 + 1) := by
    rw [padicValNat.mul (mul_ne_zero (pow_ne_zero 3 hq0) hq2sub0) hq3add0,
      padicValNat.mul (pow_ne_zero 3 hq0) hq2sub0]
  rw [hK, hq3, hq21, hq31]
  have hqadd3 : padicValNat 3 (q + 1) = 0 := padicValNat.eq_zero_of_not_dvd h3qadd
  have hq2q13 : padicValNat 3 (q ^ 2 - q + 1) = 0 := padicValNat.eq_zero_of_not_dvd h3q2q1
  rw [hqadd3, hq2q13]
  omega

private lemma exists_scalar_of_commute_of_pow_three {h : UnitaryFieldData 2 n K}
    (h3 : 3 ∣ 2 ^ n - 1) (F : SU3TorusFrame h T) {x : unitarySU 2 n K 3} (hxT : x ∈ T)
    (hx : orderOf x = 3) {y : unitarySU 2 n K 3} (hyx : y * x = x * y) (hy3 : y ^ 3 = 1) :
    ∃ α : K, α ^ 3 = 1 ∧ y • F.e = α • F.e ∧ y • F.v = F.v ∧ y • F.f = α⁻¹ • F.f := by
  classical
  have : CharP K 2 := h.charP
  obtain ⟨kx, hkx⟩ := h3
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    omega
  have hxt : (⟨x, hxT⟩ : T) ≠ 1 := by
    intro h1
    exact hx1 (congrArg Subtype.val h1)
  have hyxt : y * ((⟨x, hxT⟩ : T) : unitarySU 2 n K 3) =
      ((⟨x, hxT⟩ : T) : unitarySU 2 n K 3) * y := by
    simpa using hyx
  obtain ⟨he, hv, hf⟩ := F.smul_mem_of_commute hxt hyxt
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.mp he
  obtain ⟨β, hβ⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp hf
  have he0 := F.e_ne_zero
  have hv0 := F.v_ne_zero
  have hα3 : α ^ 3 = 1 := by
    have h := pow_smul_eq_smul_pow (a := y) (e := F.e) (c := α) hα.symm 3
    rw [hy3, one_smul] at h
    exact smul_left_injective K he0 (by simpa using h.symm)
  have hβ3 : β ^ 3 = 1 := by
    have h := pow_smul_eq_smul_pow (a := y) (e := F.v) (c := β) hβ.symm 3
    rw [hy3, one_smul] at h
    exact smul_left_injective K hv0 (by simpa using h.symm)
  have hβq : β ^ (2 ^ n - 1) = 1 := by
    rw [hkx, pow_mul, hβ3, one_pow]
  have hβnorm : h.norm β = 1 := by
    have hpres := stdHermForm_smul_smul h y F.v F.v
    rw [hβ.symm, stdHermForm_norm_smul h β F.v] at hpres
    exact mul_right_cancel₀ F.stdHermForm_v_v (by simpa using hpres)
  have hβnorm' : β * h.bar β = 1 := by
    simpa [UnitaryFieldData.norm] using hβnorm
  have hβq1 : β ^ (2 ^ n + 1) = 1 := by
    rw [pow_succ, ← h.bar_apply, mul_comm]
    exact hβnorm'
  have hβ2 : β ^ 2 = 1 := by
    have h : β ^ (2 ^ n + 1) = β ^ (2 ^ n - 1) * β ^ 2 := by
      rw [← pow_add]
      congr 1
      have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    rw [h, hβq, one_mul] at hβq1
    exact hβq1
  have hβ1 : β = 1 := mul_self_eq_one_iff_eq_one.mp (by simpa [pow_two] using hβ2)
  have hαq : α ^ (2 ^ n - 1) = 1 := by
    rw [hkx, pow_mul, hα3, one_pow]
  have hαbar : h.bar α = α := bar_eq_self_of_pow_two_pow_sub_one_eq_one h hαq
  have hαγ : h.bar α * γ = 1 := by
    have hpres : stdHermForm h 3 (α • F.e) (γ • F.f) = 1 := by
      rw [hα, hγ, ← F.stdHermForm_e_f]
      exact stdHermForm_smul_smul h y F.e F.f
    have hval : stdHermForm h 3 (α • F.e) (γ • F.f) = h.bar α * γ := by
      rw [LinearMap.map_smulₛₗ (stdHermForm h 3) α F.e, LinearMap.smul_apply,
        LinearMap.map_smul, F.stdHermForm_e_f]
      simp [smul_eq_mul]
    rwa [hval] at hpres
  have hγeq : γ = α⁻¹ := by
    rw [hαbar] at hαγ
    exact eq_inv_of_mul_eq_one_right hαγ
  refine ⟨α, hα3, ?_, ?_, ?_⟩
  · exact hα.symm
  · rw [← hβ, hβ1, one_smul]
  · rw [← hγ, hγeq]

private lemma mem_zpowers_of_commute_of_pow_three {h : UnitaryFieldData 2 n K}
    (h3 : 3 ∣ 2 ^ n - 1) (F : SU3TorusFrame h T) {x : unitarySU 2 n K 3} (hxT : x ∈ T)
    (hx : orderOf x = 3) {y : unitarySU 2 n K 3} (hyx : y * x = x * y) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.zpowers x := by
  classical
  obtain ⟨α, hα3, hαe, hαv, hαf⟩ :=
    exists_scalar_of_commute_of_pow_three h3 F hxT hx hyx hy3
  let ω : K := (F.χ ⟨x, hxT⟩ : K)
  have hω3u : (F.χ ⟨x, hxT⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have hx3T : (⟨x, hxT⟩ : T) ^ 3 = 1 := by
      apply Subtype.ext
      have h : x ^ 3 = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hx] at this
      simpa using h
    rw [hx3T, map_one]
  have hω3 : ω ^ 3 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) hω3u
    simpa [ω] using this
  have hω1 : ω ≠ 1 := by
    intro h1
    have h2 : F.χ ⟨x, hxT⟩ = 1 := Units.ext h1
    have h3 : (⟨x, hxT⟩ : T) = 1 := F.χ_injective (by rw [h2, map_one])
    exact (fun h1 => by
      have hx1 : x = 1 := by simpa using congrArg Subtype.val h1
      rw [hx1, orderOf_one] at hx
      omega) h3
  have hωprim : IsPrimitiveRoot ω 3 := by
    have horder : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
    simpa [horder] using IsPrimitiveRoot.orderOf ω
  obtain ⟨i, hi3, hi⟩ := hωprim.eq_pow_of_pow_eq_one hα3
  have he_eq : y • F.e = x ^ i • F.e := by
    rw [hαe, ← hi]
    have h := F.smul_e (⟨x, hxT⟩ ^ i)
    rw [map_pow] at h
    simpa [ω, Subgroup.coe_pow, Units.val_pow_eq_pow_val] using h.symm
  have hv_eq : y • F.v = x ^ i • F.v := by
    rw [hαv]
    simpa [Subgroup.coe_pow] using (F.smul_v (⟨x, hxT⟩ ^ i)).symm
  have hf_eq : y • F.f = x ^ i • F.f := by
    rw [hαf, ← hi]
    have h := F.smul_f (⟨x, hxT⟩ ^ i)
    rw [map_pow] at h
    simpa [ω, Subgroup.coe_pow, Units.val_pow_eq_pow_val] using h.symm
  have hy_eq : y = x ^ i := F.ext he_eq hv_eq hf_eq
  rw [hy_eq]
  exact Subgroup.mem_zpowers_iff.mpr ⟨(i : ℤ), by rw [zpow_natCast]⟩

theorem three_dvd_card {h : UnitaryFieldData 2 n K} (hn : 2 ≤ n) (h3q : 3 ∣ 2 ^ n - 1)
    (F : SU3TorusFrame h T) (hT : Nat.card T = 2 ^ n - 1) (hH : Group.IsPerfect H)
    (hTH : T ≤ Subgroup.normalizer (H : Set (unitarySU 2 n K 3)))
    (hirr : ∀ W : Submodule K (Fin 3 → K), (∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) →
      (∀ g ∈ H, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤) :
    3 ∣ Nat.card H := by
  by_contra h3H
  have : Finite K := h.finite
  have : Finite ↥(unitarySU 2 n K 3) :=
    CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts.model3U4_finite_group h
  have h3T : 3 ∣ Nat.card T := hT ▸ h3q
  obtain ⟨aT, haT3⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 3 h3T
  have haT : (aT : unitarySU 2 n K 3) ∈ T := aT.2
  have ha3 : orderOf (aT : unitarySU 2 n K 3) = 3 :=
    (Subgroup.orderOf_coe aT).trans haT3
  have ha_pow : (aT : unitarySU 2 n K 3) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (aT : unitarySU 2 n K 3)
    rwa [ha3] at this
  have haT1 : aT ≠ 1 := by
    intro h1
    have : orderOf aT = 1 := by rw [h1, orderOf_one]
    omega
  have ha_cent : (aT : unitarySU 2 n K 3) ∈
      Subgroup.centralizer (H : Set (unitarySU 2 n K 3)) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.mem_centralizer_of_isPerfect_unitarySU3
      h hn Nat.prime_three (by norm_num) ha_pow hH h3H (hTH haT)
  have hv0 := F.v_ne_zero
  let W : Submodule K (Fin 3 → K) := K ∙ F.v
  have hTW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W := by
    intro t ht w hw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
    refine Submodule.mem_span_singleton.mpr ⟨c, ?_⟩
    rw [← hc, smul_comm, F.smul_v ⟨t, ht⟩]
  have hHW : ∀ g ∈ H, ∀ w ∈ W, g • w ∈ W := by
    intro g hg w hw
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
    have hcomm : g * (aT : unitarySU 2 n K 3) = (aT : unitarySU 2 n K 3) * g :=
      (Subgroup.mem_centralizer_iff.mp ha_cent) g hg
    have hgv : g • F.v ∈ K ∙ F.v :=
      (F.smul_mem_of_commute haT1 hcomm).2.1
    obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hgv
    refine Submodule.mem_span_singleton.mpr ⟨c * d, ?_⟩
    rw [← hc, smul_comm, ← hd, smul_smul]
  rcases hirr W hTW hHW with hbot | htop
  · have hvW : F.v ∈ W := Submodule.mem_span_singleton_self F.v
    rw [hbot] at hvW
    exact hv0 (by simpa using hvW)
  · have h1 : Module.finrank K W = 1 := by
      simpa [W] using finrank_span_singleton hv0
    have h3 : Module.finrank K W = 3 := by
      rw [htop, finrank_top, Module.finrank_fin_fun]
    omega

theorem exists_mem_inf_orderOf_eq_three (h : UnitaryFieldData 2 n K) (h3q : 3 ∣ 2 ^ n - 1)
    (hT : Nat.card T = 2 ^ n - 1) (hTH : T ≤ Subgroup.normalizer (H : Set (unitarySU 2 n K 3)))
    (h3 : 3 ∣ Nat.card H) : ∃ x ∈ H ⊓ T, orderOf x = 3 := by
  classical
  have : Finite K := h.finite
  have : Finite ↥(unitarySU 2 n K 3) :=
    CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts.model3U4_finite_group h
  have hKcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, mul_comm 2 n, pow_mul]
  have hQcard : Nat.card (unitarySU 2 n K 3) =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 + 1) :=
    CFSG.SectionRank.OddCover.card_statedSU_three_of_card_eq_sq hKcard
  have hprod : Nat.card (T ⊔ H : Subgroup (unitarySU 2 n K 3)) *
      Nat.card (T ⊓ H : Subgroup (unitarySU 2 n K 3)) = Nat.card T * Nat.card H :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hTH
  have hvQ : padicValNat 3 (Nat.card (unitarySU 2 n K 3)) = padicValNat 3 (2 ^ n - 1) := by
    rw [hQcard]
    exact padicValNat_three_card_statedSU n h3q h.one_le
  have hleQ : padicValNat 3 (Nat.card (T ⊔ H : Subgroup (unitarySU 2 n K 3))) ≤
      padicValNat 3 (Nat.card (unitarySU 2 n K 3)) := by
    obtain ⟨k, hk⟩ := Subgroup.card_subgroup_dvd_card (T ⊔ H)
    have hc0 : Nat.card (T ⊔ H : Subgroup (unitarySU 2 n K 3)) ≠ 0 :=
      (Nat.card_pos : 0 < Nat.card (T ⊔ H : Subgroup (unitarySU 2 n K 3))).ne'
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      exact (Nat.card_pos : 0 < Nat.card (unitarySU 2 n K 3)).ne' hk
    rw [hk, padicValNat.mul hc0 hk0]
    exact Nat.le_add_right _ _
  have hleT : padicValNat 3 (Nat.card (T ⊔ H : Subgroup (unitarySU 2 n K 3))) ≤
      padicValNat 3 (Nat.card T) := by
    rw [hT]
    exact hleQ.trans (le_of_eq hvQ)
  have hprod' : Nat.card (T ⊔ H : Subgroup (unitarySU 2 n K 3)) *
      Nat.card (T ⊓ H : Subgroup (unitarySU 2 n K 3)) = Nat.card H * Nat.card T := by
    rw [hprod, mul_comm]
  have hd : 3 ∣ Nat.card (T ⊓ H : Subgroup (unitarySU 2 n K 3)) :=
    three_dvd_of_mul_eq (Nat.card_pos : 0 < Nat.card H).ne' (Nat.card_pos : 0 < Nat.card T).ne'
      hprod' h3 hleT
  obtain ⟨xT, hx3⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ T)) 3
    (by simpa [inf_comm] using hd)
  exact ⟨xT, xT.2, (Subgroup.orderOf_coe xT).trans hx3⟩

private lemma exists_involution_of_mem_lines {h : UnitaryFieldData 2 n K}
    (F : SU3TorusFrame h T) {m : unitarySU 2 n K 3} (hmH : m ∈ H)
    (hme : m • F.e ∈ K ∙ F.f) (hmv : m • F.v ∈ K ∙ F.v) (hmf : m • F.f ∈ K ∙ F.e) :
    ∃ z ∈ H, z ^ 2 = 1 ∧ z • F.e ∈ K ∙ F.f ∧ z • F.v ∈ K ∙ F.v ∧
      z • F.f ∈ K ∙ F.e := by
  classical
  have : Finite ↥(unitarySU 2 n K 3) :=
    CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts.model3U4_finite_group h
  obtain ⟨a, r, hr_odd, hmord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  let z : unitarySU 2 n K 3 := m ^ r
  have hzH : z ∈ H := H.pow_mem hmH r
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hme
  obtain ⟨dd, hd⟩ := Submodule.mem_span_singleton.mp hmf
  have hm2e : (m ^ 2) • F.e ∈ K ∙ F.e := by
    rw [pow_two, mul_smul, ← hc, smul_comm m c, ← hd, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hm2f : (m ^ 2) • F.f ∈ K ∙ F.f := by
    rw [pow_two, mul_smul, ← hd, smul_comm m dd, ← hc, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hm2v : (m ^ 2) • F.v ∈ K ∙ F.v := by
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hmv
    rw [pow_two, mul_smul, ← he, smul_comm m e, ← he, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have hpres : ∀ (g : unitarySU 2 n K 3) (W : Submodule K (Fin 3 → K)),
      (∀ w ∈ W, g • w ∈ W) → ∀ k : ℕ, ∀ w ∈ W, (g ^ k) • w ∈ W := by
    intro g W hW k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
        intro w hw
        rw [pow_succ, mul_smul]
        exact ih _ (hW w hw)
  obtain ⟨k, rfl⟩ := hr_odd
  have hz_eq : z = (m ^ 2) ^ k * m := by
    dsimp [z]
    rw [← pow_mul, ← pow_succ]
  have hze : z • F.e ∈ K ∙ F.f := by
    rw [hz_eq, mul_smul]
    exact hpres (m ^ 2) (K ∙ F.f) (fun w hw => by
      obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hw
      rw [← he, smul_comm (m ^ 2) e]
      exact Submodule.smul_mem _ _ hm2f) k _ hme
  have hzf : z • F.f ∈ K ∙ F.e := by
    rw [hz_eq, mul_smul]
    exact hpres (m ^ 2) (K ∙ F.e) (fun w hw => by
      obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hw
      rw [← he, smul_comm (m ^ 2) e]
      exact Submodule.smul_mem _ _ hm2e) k _ hmf
  have hzv_mem : z • F.v ∈ K ∙ F.v := by
    rw [hz_eq, mul_smul]
    exact hpres (m ^ 2) (K ∙ F.v) (fun w hw => by
      obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hw
      rw [← he, smul_comm (m ^ 2) e]
      exact Submodule.smul_mem _ _ hm2v) k _ hmv
  have hzord : z ^ (2 ^ a) = 1 := by
    dsimp [z]
    rw [← pow_mul, mul_comm (2 * k + 1) (2 ^ a), ← hmord, pow_orderOf_eq_one]
  have hz2 : z ^ 2 = 1 := by
    by_cases ha0 : a = 0
    · subst ha0
      have hr : 2 * k + 1 = orderOf m := by
        rw [hmord]
        simp
      have hz1eq : z = 1 := by
        dsimp [z]
        rw [hr]
        exact pow_orderOf_eq_one m
      rw [hz1eq, one_pow]
    · have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha0
      have hz2pow : (z ^ 2) ^ (2 ^ (a - 1)) = 1 := by
        rw [← pow_mul]
        have hexp : 2 * 2 ^ (a - 1) = 2 ^ a := by
          rw [mul_comm, ← pow_succ, Nat.sub_add_cancel ha1]
        rw [hexp, hzord]
      apply F.eq_one_of_pow_two_pow_eq_one hz2pow
      · obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hze
        rw [pow_two, mul_smul, ← he, smul_comm z e]
        exact Submodule.smul_mem _ _ hzf
      · obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hzv_mem
        rw [pow_two, mul_smul, ← he, smul_comm z e]
        exact Submodule.smul_mem _ _ hzv_mem
      · obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hzf
        rw [pow_two, mul_smul, ← he, smul_comm z e]
        exact Submodule.smul_mem _ _ hze
  exact ⟨z, hzH, hz2, hze, hzv_mem, hzf⟩

theorem exists_involution_swap {h : UnitaryFieldData 2 n K} (h3q : 3 ∣ 2 ^ n - 1)
    (F : SU3TorusFrame h T) (hH : Group.IsPerfect H) {x : unitarySU 2 n K 3} (hxH : x ∈ H)
    (hxT : x ∈ T) (hx : orderOf x = 3) :
    ∃ z ∈ H, z ^ 2 = 1 ∧ z ≠ 1 ∧ z • F.v = F.v ∧ z • F.e ∈ K ∙ F.f ∧ z • F.f ∈ K ∙ F.e := by
  classical
  have : Finite K := h.finite
  have : Finite ↥(unitarySU 2 n K 3) :=
    CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts.model3U4_finite_group h
  have : CharP K 2 := h.charP
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx
    omega
  have hxt : (⟨x, hxT⟩ : T) ≠ 1 := fun h1 => hx1 (congrArg Subtype.val h1)
  obtain ⟨m, hmH, hmx⟩ :=
    CFSG.GroupTheory.exists_conj_eq_inv_of_isPerfect (Q := unitarySU 2 n K 3) (Y := H)
      hH hxH hx fun y _ hyx hy3 =>
        mem_zpowers_of_commute_of_pow_three h3q F hxT hx hyx hy3
  have hmx' : m * ((⟨x, hxT⟩ : T) : unitarySU 2 n K 3) * m⁻¹ =
      (((⟨x, hxT⟩ : T) : unitarySU 2 n K 3))⁻¹ := by
    simpa using hmx
  obtain ⟨hme, hmv, hmf⟩ := F.smul_mem_of_conj_eq_inv hxt hmx'
  obtain ⟨z, hzH, hz2, hze, hzv_mem, hzf⟩ :=
    exists_involution_of_mem_lines F hmH hme hmv hmf
  have hv0 := F.v_ne_zero
  have hzv : z • F.v = F.v := by
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hzv_mem
    have hee : e * e = 1 := by
      have h2 : z • (z • F.v) = F.v := by rw [← mul_smul, ← pow_two, hz2, one_smul]
      rw [← he, smul_comm z e, ← he, smul_smul] at h2
      exact smul_left_injective K hv0 (by simpa using h2)
    have he1 : e = 1 := mul_self_eq_one_iff_eq_one.mp hee
    rw [← he, he1, one_smul]
  have he_not_mem : F.e ∉ K ∙ F.f := F.e_notMem_span_f
  have hz1 : z ≠ 1 := by
    intro hz
    apply he_not_mem
    have hze1 : z • F.e ∈ K ∙ F.f := hze
    rw [hz, one_smul] at hze1
    exact hze1
  exact ⟨z, hzH, hz2, hz1, hzv, hze, hzf⟩

theorem conj_eq_inv_of_swap {h : UnitaryFieldData 2 n K} (F : SU3TorusFrame h T)
    {z : unitarySU 2 n K 3} (hz2 : z ^ 2 = 1) (hzv : z • F.v = F.v) (hze : z • F.e ∈ K ∙ F.f)
    (hzf : z • F.f ∈ K ∙ F.e) {t : unitarySU 2 n K 3} (ht : t ∈ T) : z * t * z⁻¹ = t⁻¹ := by
  have he0 := F.e_ne_zero
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hz2)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hze
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hzf
  have hcd : c * d = 1 := by
    have h1 : z • (z • F.e) = F.e := by rw [← mul_smul, ← pow_two, hz2, one_smul]
    rw [← hc, smul_comm, ← hd, smul_smul] at h1
    exact smul_left_injective K he0 (by simpa using h1)
  have harg : (⟨t⁻¹, T.inv_mem ht⟩ : T) = (⟨t, ht⟩ : T)⁻¹ := Subtype.ext rfl
  have hχinv : F.χ (⟨t⁻¹, T.inv_mem ht⟩ : T) = (F.χ ⟨t, ht⟩)⁻¹ := by
    rw [harg, map_inv]
  have he_inv : ((F.χ ⟨t, ht⟩ : K)⁻¹) • F.e = t⁻¹ • F.e := by
    have h := F.smul_e (⟨t⁻¹, T.inv_mem ht⟩ : T)
    rw [hχinv] at h
    rw [show ((⟨t⁻¹, T.inv_mem ht⟩ : T) : unitarySU 2 n K 3) = t⁻¹ from rfl] at h
    rw [Units.val_inv_eq_inv_val] at h
    exact h.symm
  have hf_inv : (F.χ ⟨t, ht⟩ : K) • F.f = t⁻¹ • F.f := by
    have h := F.smul_f (⟨t⁻¹, T.inv_mem ht⟩ : T)
    rw [hχinv] at h
    rw [show ((⟨t⁻¹, T.inv_mem ht⟩ : T) : unitarySU 2 n K 3) = t⁻¹ from rfl] at h
    rw [Units.val_inv_eq_inv_val, inv_inv] at h
    exact h.symm
  apply F.ext
  · calc (z * t * z⁻¹) • F.e
        = z • (t • (z⁻¹ • F.e)) := by rw [mul_smul, mul_smul]
      _ = z • (t • (z • F.e)) := by rw [hz_inv]
      _ = z • (t • (c • F.f)) := by rw [← hc]
      _ = z • (c • (t • F.f)) := by rw [smul_comm t c]
      _ = z • (c • ((F.χ ⟨t, ht⟩ : K)⁻¹ • F.f)) := by rw [F.smul_f ⟨t, ht⟩]
      _ = z • ((c * (F.χ ⟨t, ht⟩ : K)⁻¹) • F.f) := by rw [smul_smul]
      _ = (c * (F.χ ⟨t, ht⟩ : K)⁻¹) • (z • F.f) := by
            rw [smul_comm z ((c * (F.χ ⟨t, ht⟩ : K)⁻¹) : K)]
      _ = (c * (F.χ ⟨t, ht⟩ : K)⁻¹) • (d • F.e) := by rw [← hd]
      _ = ((c * (F.χ ⟨t, ht⟩ : K)⁻¹) * d) • F.e := by rw [smul_smul]
      _ = ((F.χ ⟨t, ht⟩ : K)⁻¹) • F.e := by
            rw [show c * (F.χ ⟨t, ht⟩ : K)⁻¹ * d =
              (c * d) * (F.χ ⟨t, ht⟩ : K)⁻¹ by ring, hcd, one_mul]
      _ = t⁻¹ • F.e := he_inv
  · calc (z * t * z⁻¹) • F.v
        = z • (t • (z⁻¹ • F.v)) := by rw [mul_smul, mul_smul]
      _ = z • (t • (z • F.v)) := by rw [hz_inv]
      _ = z • (t • F.v) := by rw [hzv]
      _ = z • F.v := by rw [F.smul_v ⟨t, ht⟩]
      _ = F.v := hzv
      _ = t⁻¹ • F.v := (F.smul_v ⟨t⁻¹, T.inv_mem ht⟩).symm
  · calc (z * t * z⁻¹) • F.f
        = z • (t • (z⁻¹ • F.f)) := by rw [mul_smul, mul_smul]
      _ = z • (t • (z • F.f)) := by rw [hz_inv]
      _ = z • (t • (d • F.e)) := by rw [← hd]
      _ = z • (d • (t • F.e)) := by rw [smul_comm t d]
      _ = z • (d • ((F.χ ⟨t, ht⟩ : K) • F.e)) := by rw [F.smul_e ⟨t, ht⟩]
      _ = z • ((d * (F.χ ⟨t, ht⟩ : K)) • F.e) := by rw [smul_smul]
      _ = (d * (F.χ ⟨t, ht⟩ : K)) • (z • F.e) := by
            rw [smul_comm z ((d * (F.χ ⟨t, ht⟩ : K)) : K)]
      _ = (d * (F.χ ⟨t, ht⟩ : K)) • (c • F.f) := by rw [← hc]
      _ = ((d * (F.χ ⟨t, ht⟩ : K)) * c) • F.f := by rw [smul_smul]
      _ = (F.χ ⟨t, ht⟩ : K) • F.f := by
            rw [show d * (F.χ ⟨t, ht⟩ : K) * c =
              (c * d) * (F.χ ⟨t, ht⟩ : K) by ring, hcd, one_mul]
      _ = t⁻¹ • F.f := hf_inv

theorem le_of_swap {h : UnitaryFieldData 2 n K} (F : SU3TorusFrame h T) (hT : Odd (Nat.card T))
    (hTH : T ≤ Subgroup.normalizer (H : Set (unitarySU 2 n K 3))) {z : unitarySU 2 n K 3}
    (hzH : z ∈ H) (hz2 : z ^ 2 = 1) (hzv : z • F.v = F.v) (hze : z • F.e ∈ K ∙ F.f)
    (hzf : z • F.f ∈ K ∙ F.e) : T ≤ H := by
  intro t ht
  have hzn : t * z * t⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp (hTH ht) z).mp hzH
  have ht_eq : t = z * t⁻¹ * z⁻¹ := by
    have h := conj_eq_inv_of_swap F hz2 hzv hze hzf (T.inv_mem ht)
    simpa using h.symm
  have ht2 : t ^ 2 ∈ H := by
    have h2 : t ^ 2 = (t * z * t⁻¹) * z⁻¹ := by
      rw [pow_two]
      nth_rw 2 [ht_eq]
      group
    rw [h2]
    exact H.mul_mem hzn (H.inv_mem hzH)
  obtain ⟨k, hk⟩ := hT
  have htcard : t ^ (2 * k + 1) = 1 := by
    have h : (⟨t, ht⟩ : T) ^ (2 * k + 1) = 1 := by
      simpa [hk] using pow_card_eq_one' (x := (⟨t, ht⟩ : T))
    simpa using congrArg Subtype.val h
  have ht_pow : t = (t ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = 2 * k + 1 + 1 by omega, pow_succ, htcard, one_mul]
  rw [ht_pow]
  exact H.pow_mem ht2 (k + 1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3TorusIrred
