module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_conj_zpow_inv {A : Type*} [Group A] {t x : A}
    (h : t * x * t⁻¹ = x⁻¹) (n : ℤ) : t * x ^ n * t⁻¹ = (x ^ n)⁻¹ := by
  have hconj : MulAut.conj t x = x⁻¹ := by rw [MulAut.conj_apply, h]
  calc t * x ^ n * t⁻¹ = MulAut.conj t (x ^ n) := (MulAut.conj_apply t (x ^ n)).symm
    _ = (MulAut.conj t x) ^ n := map_zpow (MulAut.conj t) x n
    _ = (x⁻¹) ^ n := by rw [hconj]
    _ = (x ^ n)⁻¹ := by rw [inv_zpow]

theorem exists_mem_ne_one_inverted {A : Type*} [Group A] {t : A} (ht : t * t = 1)
    {P : Subgroup A} (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) (hc : ⁅P, Subgroup.zpowers t⁆ ≠ ⊥) :
    ∃ z ∈ P, z ≠ 1 ∧ t * z * t⁻¹ = z⁻¹ := by
  by_cases hfix : ∀ y ∈ P, t * y * t⁻¹ = y
  · have hle : P ≤ Subgroup.centralizer (Subgroup.zpowers t) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
      have hty : Commute t y := by
        show t * y = y * t
        calc t * y = t * y * t⁻¹ * t := by group
          _ = y * t := by rw [hfix y hy]
      rw [← hk]
      exact (hty.zpow_left k).eq
    exact absurd (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle) hc
  · push Not at hfix
    obtain ⟨y, hy, hne⟩ := hfix
    refine ⟨y⁻¹ * (t * y * t⁻¹), P.mul_mem (P.inv_mem hy) (hn y hy), ?_, ?_⟩
    · intro h1
      apply hne
      calc t * y * t⁻¹ = y * (y⁻¹ * (t * y * t⁻¹)) := by group
        _ = y * 1 := by rw [h1]
        _ = y := by simp
    · have hφ : MulAut.conj t (MulAut.conj t y) = y := by
        have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
        rw [MulAut.conj_apply, MulAut.conj_apply, htinv]
        calc t * (t * y * t) * t = t * t * y * (t * t) := by group
          _ = y := by simp [ht]
      have hz : y⁻¹ * (t * y * t⁻¹) = y⁻¹ * MulAut.conj t y := by rw [MulAut.conj_apply]
      calc t * (y⁻¹ * (t * y * t⁻¹)) * t⁻¹
          = MulAut.conj t (y⁻¹ * (t * y * t⁻¹)) := (MulAut.conj_apply t _).symm
        _ = MulAut.conj t (y⁻¹ * MulAut.conj t y) := by rw [hz]
        _ = (MulAut.conj t y)⁻¹ * y := by rw [map_mul, map_inv, hφ]
        _ = (y⁻¹ * (t * y * t⁻¹))⁻¹ := by rw [hz, mul_inv_rev, inv_inv]

theorem exists_inverted_orderOf_eq_prime {A : Type*} [Group A] [Finite A] {t : A}
    (ht : t * t = 1) {p : ℕ} (hp : p.Prime) {P : Subgroup A} (hP : IsPGroup p ↥P)
    (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) (hc : ⁅P, Subgroup.zpowers t⁆ ≠ ⊥) :
    ∃ x ∈ P, orderOf x = p ∧ t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨z, hzP, hz1, hzinv⟩ := exists_mem_ne_one_inverted ht hn hc
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hP.exists_orderOf_eq_pow (⟨z, hzP⟩ : ↥P)
  have hzord : orderOf z = p ^ k := by
    rw [← Subgroup.orderOf_mk z hzP]
    exact hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hzord
    exact hz1 (orderOf_eq_one_iff.mp hzord)
  have hzne0 : orderOf z ≠ 0 := by
    rw [hzord]
    exact pow_ne_zero k hp.ne_zero
  have hdvd : p ∣ orderOf z := by
    rw [hzord]
    exact dvd_pow_self p hk0
  let x : A := z ^ (orderOf z / p)
  have hxord : orderOf x = p := by
    dsimp only [x]
    exact orderOf_pow_orderOf_div hzne0 hdvd
  have hxinv : t * x * t⁻¹ = x⁻¹ := by
    dsimp only [x]
    rw [← zpow_natCast]
    exact w16g_conj_zpow_inv hzinv _
  exact ⟨x, P.pow_mem hzP _, hxord, hxinv⟩

theorem eq_bot_of_isPGroup_two_of_comm_eq_self {A : Type*} [Group A] [Finite A] {t : A}
    (ht : t * t = 1) {P : Subgroup A} (hP : IsPGroup 2 ↥P) (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (hc : ⁅P, Subgroup.zpowers t⁆ = P) : P = ⊥ := by
  by_contra hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  have ht_norm : t ∈ Subgroup.normalizer P := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hn y hy, fun hy => ?_⟩
    have hcalc : t * (t * y * t⁻¹) * t⁻¹ = y := by
      rw [htinv]
      calc t * (t * y * t) * t = t * t * y * (t * t) := by group
        _ = y := by simp [ht]
    have := hn (t * y * t⁻¹) hy
    rwa [hcalc] at this
  have hK_norm : Subgroup.zpowers t ≤ Subgroup.normalizer P :=
    Subgroup.zpowers_le.mpr ht_norm
  have hKp : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr (by simpa [pow_two] using ht)
  let G : Subgroup A := P ⊔ Subgroup.zpowers t
  have hG : IsPGroup 2 ↥G := by
    dsimp only [G]
    exact IsPGroup.to_sup_of_normal_left' (p := 2) hP hKp hK_norm
  haveI : Finite ↥G := Finite.of_injective (Subtype.val : ↥G → A) Subtype.val_injective
  have hnil : Group.IsNilpotent ↥G := IsPGroup.isNilpotent hG
  obtain ⟨c, hcG⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries (S := G)).mp hnil
  have hle : ∀ n, P ≤ G.lowerCentralSeries n := by
    intro n
    induction n with
    | zero =>
        show P ≤ G
        dsimp only [G]
        exact le_sup_left
    | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ]
        calc P = ⁅P, Subgroup.zpowers t⁆ := hc.symm
          _ ≤ ⁅P, G⁆ := by
              apply Subgroup.commutator_mono le_rfl
              dsimp only [G]
              exact le_sup_right
          _ ≤ ⁅G.lowerCentralSeries n, G⁆ := Subgroup.commutator_mono ih le_rfl
  have hbot : P ≤ ⊥ := by
    have := hle c
    rwa [hcG] at this
  exact hne (le_bot_iff.mp hbot)

private theorem w16g_dParam_le_dihedralDeg (p : ℕ) : dParam p ≤ dihedralDeg p := by
  unfold dihedralDeg
  split
  · rfl
  · omega

private theorem w16g_eq_five_of_prime_gt_seven {p d : ℕ} (hp : p.Prime) (h7 : 7 < p)
    (hd1 : 1 ≤ d) (hd6 : d ≤ 6) (hdiv : p ∣ 2 ^ d - 1) : d = 5 := by
  interval_cases d
  · exfalso
    norm_num at hdiv
    have := hp.two_le
    omega
  · exfalso
    norm_num at hdiv
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hdiv
    omega
  · exfalso
    norm_num at hdiv
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp hdiv
    omega
  · exfalso
    have h : p ∣ 3 * 5 := by norm_num at hdiv ⊢; exact hdiv
    rcases hp.dvd_mul.mp h with h3 | h5
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5
      omega
  · rfl
  · exfalso
    have h : p ∣ 3 * 21 := by norm_num at hdiv ⊢; exact hdiv
    rcases hp.dvd_mul.mp h with h3 | h21
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
      omega
    · have h' : p ∣ 3 * 7 := by norm_num at h21 ⊢; exact h21
      rcases hp.dvd_mul.mp h' with h3' | h7'
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h7'
        omega

theorem six_lt_dihedralDeg_of_seven_lt {p : ℕ} (hp : p.Prime) (h7 : 7 < p) :
    6 < dihedralDeg p := by
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at h7
    norm_num at h7
  by_cases hd : 6 < dParam p
  · have := w16g_dParam_le_dihedralDeg p
    omega
  · push Not at hd
    have h1 : 1 ≤ 2 ^ dParam p := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
    have h2d : ((2 ^ dParam p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      push_cast
      rw [pow_dParam p]
    have hmod : 2 ^ dParam p ≡ 1 [MOD p] :=
      (ZMod.natCast_eq_natCast_iff (2 ^ dParam p) 1 p).mp h2d
    have hdiv : p ∣ 2 ^ dParam p - 1 :=
      (Nat.modEq_iff_dvd' (n := p) (a := 1) (b := 2 ^ dParam p) h1).mp hmod.symm
    have hd1 : 1 ≤ dParam p := by
      have := dParam_pos hp hp2
      omega
    have h5 : dParam p = 5 := w16g_eq_five_of_prime_gt_seven hp h7 hd1 hd hdiv
    have hD : dihedralDeg p = 10 := by
      simp only [dihedralDeg]
      rw [h5]
      norm_num
    omega

theorem le_seven_of_comm_eq_self (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W} (ht : orderOf t = 2)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) {p : ℕ} (hp : p.Prime)
    {P : Subgroup (MulAut W)} (hP : IsPGroup p ↥P) (hne : P ≠ ⊥)
    (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P) (hc : ⁅P, Subgroup.zpowers t⁆ = P) : p ≤ 7 := by
  by_contra hle
  have h8 : 7 < p := by omega
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at h8
    norm_num at h8
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht, pow_two] at this
    exact this
  have hcne : ⁅P, Subgroup.zpowers t⁆ ≠ ⊥ := by
    rw [hc]
    exact hne
  obtain ⟨x, _hxP, hxord, hxinv⟩ := exists_inverted_orderOf_eq_prime htt hp hP hn hcne
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard1 : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hxord]
  have hcard2 : Nat.card (Multiplicative (Fin 1 → ZMod p)) = p := by
    simp [Nat.card_eq_fintype_card]
  haveI : IsCyclic (Multiplicative (Fin 1 → ZMod p)) :=
    isCyclic_of_prime_card hcard2
  have hX : IsElemAbelianOfRank p 1 ↥(Subgroup.zpowers x) :=
    ⟨mulEquivOfCyclicCardEq (hcard1.trans hcard2.symm)⟩
  have hinvX : ∀ y ∈ Subgroup.zpowers x, t * y * t⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hk]
    exact w16g_conj_zpow_inv hxinv k
  have hbridge := n_mul_dihedralDeg_le_two_mul_rk hW ht hp hp2 Nat.one_pos hX hinvX
  have hsix := six_lt_dihedralDeg_of_seven_lt hp h8
  have : dihedralDeg p ≤ 6 := by
    have h2 : 2 * rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 6 := by omega
    omega
  omega

end CFSG.LocalAnalysis.WeakClosure81
