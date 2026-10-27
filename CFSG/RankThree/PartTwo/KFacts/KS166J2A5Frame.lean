module

public import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Alt5
public import CFSG.RankThree.PartTwo.KFacts.KS166J2A5V
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.J2
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.GroupTheory.PGroupFixedPointCongruence

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS166

open Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover

variable {K : Subgroup GJ}

private theorem zJ_mem_centralizer
    (hKz : K ≤ centralizer ({zJ} : Set GJ)) : zJ ∈ centralizer (K : Set GJ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.1 (hKz hk)

private theorem centralizer_le_centralizer_x
    (hxK : xJ ∈ K) :
    centralizer (K : Set GJ) ≤ centralizer ({xJ} : Set GJ) :=
  Subgroup.centralizer_le (by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hxK)

private theorem VJ_le_centralizer_VJ :
    VJ ≤ centralizer (VJ : Set GJ) := by
  haveI : IsMulCommutative VJ :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := VJ) (p := 2) (by
      rw [card_V]
      norm_num)
  exact Subgroup.le_centralizer (H := VJ)

theorem VJ_le_centralizer
    (hKA : Nonempty (↥K ≃* alternatingGroup (Fin 5))) (hxK : xJ ∈ K)
    (hKz : K ≤ centralizer ({zJ} : Set GJ)) : VJ ≤ centralizer (K : Set GJ) := by
  obtain ⟨φ⟩ := hKA
  obtain ⟨t, htK, ht2, ht1, ht5⟩ := exists_inv_of_pow_three φ hxK x_cube xJ_ne_one
  have htCV : t ∈ centralizer (VJ : Set GJ) :=
    mem_centralizer_VJ_of_inv (hKz htK) ht2 ht1 ht5
  have hxCV : xJ ∈ centralizer (VJ : Set GJ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.1 (V_le_C hv)
  set H : Subgroup GJ := K ⊓ centralizer (VJ : Set GJ) with hH
  have hxH : xJ ∈ H := ⟨hxK, hxCV⟩
  have htH : t ∈ H := ⟨htK, htCV⟩
  have hxtH : xJ * t ∈ H := H.mul_mem hxH htH
  have hord2 : orderOf t = 2 := orderOf_eq_prime (p := 2) (by rwa [pow_two]) ht1
  have hord3 : orderOf xJ = 3 := orderOf_eq_prime (p := 3) x_cube xJ_ne_one
  have hxt1 : xJ * t ≠ 1 := by
    intro h
    have ht_eq : t = xJ⁻¹ := eq_inv_of_mul_eq_one_right h
    have ht3 : t ^ 3 = 1 := by
      rw [ht_eq, inv_pow, x_cube, inv_one]
    have h3 : orderOf t = 3 := orderOf_eq_prime (p := 3) ht3 ht1
    omega
  have hord5 : orderOf (xJ * t) = 5 := orderOf_eq_prime (p := 5) ht5 hxt1
  have h2dvd : 2 ∣ Nat.card H := by
    have h := Subgroup.orderOf_dvd_natCard H htH
    rwa [hord2] at h
  have h3dvd : 3 ∣ Nat.card H := by
    have h := Subgroup.orderOf_dvd_natCard H hxH
    rwa [hord3] at h
  have h5dvd : 5 ∣ Nat.card H := by
    have h := Subgroup.orderOf_dvd_natCard H hxtH
    rwa [hord5] at h
  have h6 : 6 ∣ Nat.card H :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2dvd h3dvd
  have h30 : 30 ∣ Nat.card H :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h6 h5dvd
  have hEq : H = K := eq_of_thirty_dvd φ inf_le_left h30
  have hKV : K ≤ centralizer (VJ : Set GJ) := by
    rw [← hEq]
    exact inf_le_right
  exact Subgroup.le_centralizer_iff.mp hKV

theorem centralizer_eq
    (hKA : Nonempty (↥K ≃* alternatingGroup (Fin 5))) (hxK : xJ ∈ K)
    (hKz : K ≤ centralizer ({zJ} : Set GJ)) :
    centralizer (K : Set GJ) = VJ ⊔ zpowers zJ := by
  obtain ⟨φ⟩ := hKA
  have hleCK : VJ ⊔ zpowers zJ ≤ centralizer (K : Set GJ) := by
    refine sup_le (VJ_le_centralizer ⟨φ⟩ hxK hKz) ?_
    exact zpowers_le.2 (zJ_mem_centralizer hKz)
  have hleCx : centralizer (K : Set GJ) ≤ centralizer ({xJ} : Set GJ) :=
    centralizer_le_centralizer_x hxK
  have h12dvd : 12 ∣ Nat.card (centralizer (K : Set GJ)) := by
    have h := Subgroup.card_dvd_of_le hleCK
    rwa [card_sup_VJ_zpowers_z] at h
  have h36dvd : Nat.card (centralizer (K : Set GJ)) ∣ 36 := by
    have h := Subgroup.card_dvd_of_le hleCx
    rwa [CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.card_centralizer_xJ] at h
  have hcard : Nat.card (centralizer (K : Set GJ)) = 12 := by
    obtain ⟨a, ha⟩ := h12dvd
    obtain ⟨b, hb⟩ := h36dvd
    have hab : a * b = 3 := by
      have h : 12 * (a * b) = 12 * 3 := by
        calc 12 * (a * b) = (12 * a) * b := by ring
          _ = Nat.card (centralizer (K : Set GJ)) * b := by rw [← ha]
          _ = 36 := hb.symm
          _ = 12 * 3 := by norm_num
      exact Nat.eq_of_mul_eq_mul_left (n := 12) (by norm_num) h
    have ha13 : a = 1 ∨ a = 3 := (Nat.dvd_prime Nat.prime_three).mp ⟨b, hab.symm⟩
    rcases ha13 with rfl | rfl
    · rw [ha, mul_one]
    · exfalso
      have h36 : Nat.card (centralizer (K : Set GJ)) = 36 := by
        rw [ha, show 12 * 3 = 36 by norm_num]
      have heq : centralizer (K : Set GJ) = centralizer ({xJ} : Set GJ) :=
        Subgroup.eq_of_le_of_card_ge hleCx (by
          simp [h36, CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.card_centralizer_xJ])
      have hxJC : xJ ∈ centralizer (K : Set GJ) := by
        rw [heq, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
      have hcomm : ∀ y : ↥K, (⟨xJ, hxK⟩ : ↥K) * y = y * ⟨xJ, hxK⟩ := by
        intro y
        apply Subtype.ext
        show xJ * (y : GJ) = (y : GJ) * xJ
        exact ((Subgroup.mem_centralizer_iff.1 hxJC) (y : GJ) y.2).symm
      have hxJ1 : (⟨xJ, hxK⟩ : ↥K) = 1 := eq_one_of_commute_alt5 φ hcomm
      exact xJ_ne_one (by simpa using congrArg (fun z : ↥K => (z : GJ)) hxJ1)
  have heq : VJ ⊔ zpowers zJ = centralizer (K : Set GJ) :=
    Subgroup.eq_of_le_of_card_ge hleCK (by simp [hcard, card_sup_VJ_zpowers_z])
  exact heq.symm

theorem card_centralizer
    (hKA : Nonempty (↥K ≃* alternatingGroup (Fin 5))) (hxK : xJ ∈ K)
    (hKz : K ≤ centralizer ({zJ} : Set GJ)) :
    Nat.card (centralizer (K : Set GJ)) = 12 := by
  rw [centralizer_eq hKA hxK hKz, card_sup_VJ_zpowers_z]

theorem isSolvable_centralizer
    (hKA : Nonempty (↥K ≃* alternatingGroup (Fin 5))) (hxK : xJ ∈ K)
    (hKz : K ≤ centralizer ({zJ} : Set GJ)) :
    Group.IsSolvable ↥(centralizer (K : Set GJ)) := by
  refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
  rw [card_centralizer hKA hxK hKz, show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
    Nat.prime_three.primeFactors]
  decide

theorem pCoreOf_centralizer
    (hKA : Nonempty (↥K ≃* alternatingGroup (Fin 5))) (hxK : xJ ∈ K)
    (hKz : K ≤ centralizer ({zJ} : Set GJ)) :
    CFSG.Open.pCoreOf 2 (centralizer (K : Set GJ)) = VJ := by
  change inSubgroup (CFSG.pCore 2) (centralizer (K : Set GJ)) = VJ
  refine inSubgroup_pCore_eq (VJ_le_centralizer hKA hxK hKz) ?_ isPGroup_V ?_
  · exact normal_V_in ((centralizer_le_centralizer_x hxK).trans
      (centralizer_le_normalizer_zpowers' xJ))
  · intro w hw
    obtain ⟨hwC, h2⟩ := two_of_mem_inSubgroup_pCore hw
    exact mem_V_of_two ((centralizer_le_centralizer_x hxK) hwC) (pow128 h2)

theorem centralizer_inf_centralizer_VJ
    (hKA : Nonempty (↥K ≃* alternatingGroup (Fin 5))) (hxK : xJ ∈ K)
    (hKz : K ≤ centralizer ({zJ} : Set GJ)) :
    centralizer (K : Set GJ) ⊓ centralizer (VJ : Set GJ) = VJ := by
  set D : Subgroup GJ := centralizer (K : Set GJ) ⊓ centralizer (VJ : Set GJ) with hD
  have hVK : VJ ≤ centralizer (K : Set GJ) := VJ_le_centralizer hKA hxK hKz
  have hVV : VJ ≤ centralizer (VJ : Set GJ) := VJ_le_centralizer_VJ
  have hVinf : VJ ≤ D := le_inf hVK hVV
  have hdvd : Nat.card D ∣ 12 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : D ≤ centralizer (K : Set GJ))
    rwa [card_centralizer hKA hxK hKz] at h
  have h4dvd : 4 ∣ Nat.card D := by
    have h := Subgroup.card_dvd_of_le hVinf
    rwa [card_V] at h
  have hcardD : Nat.card D = 4 := by
    obtain ⟨a, ha⟩ := hdvd
    obtain ⟨b, hb⟩ := h4dvd
    have hba : b * a = 3 := by
      have h : 4 * (b * a) = 4 * 3 := by
        calc 4 * (b * a) = (4 * b) * a := by ring
          _ = Nat.card D * a := by rw [← hb]
          _ = 12 := ha.symm
          _ = 4 * 3 := by norm_num
      exact Nat.eq_of_mul_eq_mul_left (n := 4) (by norm_num) h
    have hb13 : b = 1 ∨ b = 3 := (Nat.dvd_prime Nat.prime_three).mp ⟨a, hba.symm⟩
    rcases hb13 with rfl | rfl
    · rw [hb, mul_one]
    · exfalso
      have h12 : Nat.card D = 12 := by rw [hb, show 4 * 3 = 12 by norm_num]
      have heq : D = centralizer (K : Set GJ) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by
          simp [h12, card_centralizer hKA hxK hKz])
      have hzD : zJ ∈ D := by
        rw [heq]
        exact zJ_mem_centralizer hKz
      have hzCV : zJ ∈ centralizer (VJ : Set GJ) := (Subgroup.mem_inf.mp hzD).2
      have hVJleCz : VJ ≤ centralizer ({zJ} : Set GJ) := by
        intro v hv
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact ((Subgroup.mem_centralizer_iff.1 hzCV) v hv).symm
      have hle : VJ ≤ VJ ⊓ centralizer ({zJ} : Set GJ) := le_inf le_rfl hVJleCz
      rw [VJ_inf_centralizer_z] at hle
      have hbot : VJ = ⊥ := le_bot_iff.mp hle
      have hcardV : Nat.card VJ = 1 := by rw [hbot, Subgroup.card_bot]
      rw [card_V] at hcardV
      exact absurd hcardV (by norm_num)
  have hEq : VJ = D :=
    Subgroup.eq_of_le_of_card_ge hVinf (by simp [hcardD, card_V])
  exact hEq.symm

theorem eq_bot_or_eq_VJ
    (hxK : xJ ∈ K) {U : Subgroup GJ}
    (hU : U ≤ centralizer (K : Set GJ)) (hU2 : IsPGroup 2 U)
    (hzU : zJ ∈ normalizer (U : Set GJ)) : U = ⊥ ∨ U = VJ := by
  have hUCx : U ≤ centralizer ({xJ} : Set GJ) := hU.trans (centralizer_le_centralizer_x hxK)
  have hUV : U ≤ VJ := by
    intro u hu
    exact mem_V_of_two (hUCx hu) (pow128 (two_of_mem hU2 hu))
  have hX : IsPGroup 3 (zpowers zJ) :=
    IsPGroup.of_card (p := 3) (n := 1) (by rw [card_zpowers_z]; norm_num)
  have hXW : zpowers zJ ≤ normalizer (U : Set GJ) := zpowers_le.2 hzU
  have hC : U ⊓ centralizer ((zpowers zJ : Subgroup GJ) : Set GJ) = ⊥ := by
    rw [centralizer_zpowers_eq]
    refine le_antisymm ?_ bot_le
    intro g hg
    obtain ⟨hgU, hgC⟩ := Subgroup.mem_inf.mp hg
    rw [← VJ_inf_centralizer_z]
    exact ⟨hUV hgU, hgC⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod : Nat.card U ≡ 1 [MOD 3] :=
    CFSG.GroupTheory.card_modEq_one_of_isPGroup_normalizes_of_inf_centralizer_eq_bot hX hXW hC
  have hdvd : Nat.card U ∣ 4 := by
    have h := Subgroup.card_dvd_of_le hUV
    rwa [card_V] at h
  have hmod' : Nat.card U % 3 = 1 := by
    have h := hmod
    norm_num at h
    exact h
  obtain ⟨c, hc⟩ := hdvd
  have hc_dvd : c ∣ 4 := ⟨Nat.card U, by rw [mul_comm]; exact hc⟩
  have hc_le : c ≤ 4 := Nat.le_of_dvd (by norm_num) hc_dvd
  have hc_pos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, mul_zero] at hc
      omega
    · exact h
  interval_cases c
  · right
    have hcardU : Nat.card U = 4 := by omega
    exact Subgroup.eq_of_le_of_card_ge hUV (by simp [card_V, hcardU])
  · exfalso
    have hcardU : Nat.card U = 2 := by omega
    rw [hcardU] at hmod'
    exact absurd hmod' (by decide)
  · exfalso
    omega
  · left
    have hcardU : Nat.card U = 1 := by omega
    exact Subgroup.card_eq_one.mp hcardU

end CFSG.RankThree.PartTwo.KFacts.KS166
