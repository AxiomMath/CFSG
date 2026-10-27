module

public import CFSG.LocalAnalysis.StandardType.GGHalfEndNodes
public import CFSG.LocalAnalysis.StandardType.GGHalfZpowers

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem ggHalfInnerLine_zpow_mod {G : Type} [Group G] {g : G} (hg : g ^ 3 = 1) (k : ℤ) :
    g ^ k = g ^ (k % 3) := by
  have hg3 : g ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, _root_.zpow_natCast]
    exact hg
  conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
  rw [_root_.zpow_add, _root_.zpow_mul, hg3, _root_.one_zpow, mul_one]

private theorem ggHalfInnerLine_zpow_eq_one_of_three_dvd {G : Type} [Group G] {g : G}
    (hg : g ^ 3 = 1) {k : ℤ} (hk : (3 : ℤ) ∣ k) : g ^ k = 1 := by
  have hg3 : g ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, _root_.zpow_natCast]
    exact hg
  obtain ⟨t, ht⟩ := hk
  rw [ht, _root_.zpow_mul, hg3, _root_.one_zpow]

private theorem ggHalfInnerLine_zpowers_zpow_eq_of_three {G : Type} [Group G] {g : G}
    (hg : g ^ 3 = 1) {k : ℤ} (hk : ¬ (3 : ℤ) ∣ k) :
    Subgroup.zpowers (g ^ k) = Subgroup.zpowers g := by
  have hg3 : g ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, _root_.zpow_natCast]
    exact hg
  have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by
    have h0 : k % 3 ≠ 0 := fun h0 => hk (Int.dvd_of_emod_eq_zero h0)
    omega
  have hred : g ^ k = g ^ (k % 3) := ggHalfInnerLine_zpow_mod hg k
  rcases hk3 with h | h
  · have hk1 : g ^ k = g := by rw [hred, h, _root_.zpow_one]
    rw [hk1]
  · have hk2 : g ^ k = g⁻¹ := by
      rw [hred, h]
      apply eq_inv_of_mul_eq_one_left
      rw [← hg]
      group
    rw [hk2, Subgroup.zpowers_inv]

private theorem ggHalfInnerLine_emod_cases {k : ℤ} (hk : ¬ (3 : ℤ) ∣ k) :
    k % 3 = 1 ∨ k % 3 = 2 := by
  have h0 : k % 3 ≠ 0 := fun h0 => hk (Int.dvd_of_emod_eq_zero h0)
  omega

private theorem ggHalfInnerLine_mixed {G : Type} [Group G] {a b z : G}
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : Commute a b)
    {I J : ℤ} (hI : ¬ (3 : ℤ) ∣ I) (hJ : ¬ (3 : ℤ) ∣ J)
    (hz : z = a ^ J * b ^ I) :
    Subgroup.zpowers z = Subgroup.zpowers (a * b) ∨
      Subgroup.zpowers z = Subgroup.zpowers (a * b ^ 2) := by
  have hzred : z = a ^ (J % 3) * b ^ (I % 3) := by
    rw [hz, ggHalfInnerLine_zpow_mod ha J, ggHalfInnerLine_zpow_mod hb I]
  have hJ3 : J % 3 = 1 ∨ J % 3 = 2 := ggHalfInnerLine_emod_cases hJ
  have hI3 : I % 3 = 1 ∨ I % 3 = 2 := ggHalfInnerLine_emod_cases hI
  have hab2 : Commute a (b ^ 2) := hab.pow_right 2
  have hg1 : (a * b) ^ 3 = 1 := by rw [hab.mul_pow 3, ha, hb, mul_one]
  have hg2 : (a * b ^ 2) ^ 3 = 1 := by
    rw [hab2.mul_pow 3]
    have hb6 : (b ^ 2) ^ 3 = 1 := by
      rw [← pow_mul b 2 3, show (2 * 3 : ℕ) = 3 * 2 by omega, pow_mul b 3 2, hb,
        one_pow]
    rw [hb6, ha, mul_one]
  have hsq : (a * b ^ 2) ^ (2 : ℤ) = a ^ (2 : ℤ) * b := by
    simp only [zpow_ofNat]
    rw [hab2.mul_pow 2]
    have hb22 : (b ^ 2) ^ 2 = b ^ 4 := by rw [← pow_mul]
    have hb4 : b ^ 4 = b := by
      rw [show (4 : ℕ) = 1 + 3 by omega, pow_add, pow_one, hb, mul_one]
    rw [hb22, hb4]
  rcases hJ3 with hJ1 | hJ2 <;> rcases hI3 with hI1 | hI2
  · left
    rw [hzred, hJ1, hI1]
    simp only [_root_.zpow_one]
  · right
    rw [hzred, hJ1, hI2]
    simp only [_root_.zpow_one, zpow_ofNat, pow_one]
  · right
    rw [hzred, hJ2, hI1]
    simp only [_root_.zpow_one]
    rw [← hsq]
    exact ggHalfInnerLine_zpowers_zpow_eq_of_three (g := a * b ^ 2) hg2 (by norm_num)
  · left
    rw [hzred, hJ2, hI2]
    rw [← hab.mul_zpow 2]
    exact ggHalfInnerLine_zpowers_zpow_eq_of_three (g := a * b) hg1 (by norm_num)

theorem nbr_line {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J K : Subgroup G} {m : ℕ} {y : G}
    {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂) {y' : G} {K' : Subgroup G}
    (hnbr : GGNbr p B x D J y' K') :
    Subgroup.zpowers y' = Subgroup.zpowers y ∨
      ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ Subgroup.zpowers y' = Subgroup.zpowers (vElt φ₁ * wElt φ₂ ^ e) := by
  obtain ⟨-, hp3, -, -, hNbrY, -, -⟩ := h.nbr
  subst hp3
  obtain ⟨hcommBs, hpow3, hxBs, -, hxne, -, -, -, -, -⟩ := h.basic
  have hS : LargeEvenStdSub 3 B x L D J := h.cfg.2.2
  have hBs : GGBstar 3 B Bs := h.cfg.2.1
  have hv3 : (vElt φ₁) ^ 3 = 1 := hpow3 (vElt φ₁) h.vElt_mem
  have hw3 : (wElt φ₂) ^ 3 = 1 := hpow3 (wElt φ₂) h.wElt_mem
  have hcomm_vw : Commute (vElt φ₁) (wElt φ₂) :=
    hcommBs (vElt φ₁) h.vElt_mem (wElt φ₂) h.wElt_mem
  have hDpair : D = Subgroup.closure ({x, y'} : Set G) := hnbr.2.1
  have hy'D : y' ∈ D := by
    rw [hDpair]
    exact Subgroup.subset_closure (by simp)
  have hy'Bs : y' ∈ Bs := hBs.1 (hS.1.1 hy'D)
  have hy'ne : y' ≠ 1 := hnbr.1.2.2.1
  have hnotx : y' ∉ Subgroup.zpowers x := by
    intro hyx
    have hle : D ≤ Subgroup.zpowers x := by
      rw [hDpair, Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg
      · rw [hg]; exact Subgroup.mem_zpowers x
      · rw [hg]; exact hyx
    have hcardle : Nat.card D ≤ orderOf x := by
      have h := Subgroup.card_le_of_le hle
      rwa [Nat.card_zpowers] at h
    have hxord : orderOf x = 3 := by
      have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact orderOf_eq_prime (hpow3 x hxBs) hxne
    have hD9 : Nat.card D = 9 := by
      rw [hS.1.2.2.1]
      norm_num
    rw [hxord] at hcardle
    omega
  have hJcent : J ≤ Subgroup.centralizer (D : Set G) :=
    (hS.1.2.2.2.2.2.1.1).trans inf_le_right
  have hy'J : ∀ j ∈ J, y' * j = j * y' := by
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp (hJcent hj)) y' hy'D
  obtain ⟨i, j, hy⟩ := h.exists_eq_x_pow_mul_v_pow hy'Bs hy'J
  have hxw : x ∈ Subgroup.zpowers (wElt φ₂) := by
    change x ∈ Subgroup.zpowers (φ₂ (omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩))
    rw [← h.zpowers_x]
    exact Subgroup.mem_zpowers x
  obtain ⟨a, ha⟩ := (Subgroup.mem_zpowers_iff).mp hxw
  have hxi : wElt φ₂ ^ (a * i) = x ^ i := by
    rw [_root_.zpow_mul, ha]
  have hydecomp : y' = vElt φ₁ ^ j * wElt φ₂ ^ (a * i) := by
    rw [hy, ← hxi]
    exact (hcomm_vw.zpow_zpow j (a * i)).eq.symm
  by_cases hI : (3 : ℤ) ∣ a * i
  · left
    have hwI : wElt φ₂ ^ (a * i) = 1 := ggHalfInnerLine_zpow_eq_one_of_three_dvd hw3 hI
    have hyv : y' = vElt φ₁ ^ j := by rw [hydecomp, hwI, mul_one]
    have hJ : ¬ (3 : ℤ) ∣ j := by
      intro hJd
      have hvJ : vElt φ₁ ^ j = 1 := ggHalfInnerLine_zpow_eq_one_of_three_dvd hv3 hJd
      exact hy'ne (by rw [hyv, hvJ])
    calc Subgroup.zpowers y' = Subgroup.zpowers (vElt φ₁ ^ j) := by rw [hyv]
      _ = Subgroup.zpowers (vElt φ₁) := ggHalfInnerLine_zpowers_zpow_eq_of_three hv3 hJ
      _ = Subgroup.zpowers y := by simpa only [vElt] using h.zpowers_y.symm
  · by_cases hJ : (3 : ℤ) ∣ j
    · exfalso
      have hvJ : vElt φ₁ ^ j = 1 := ggHalfInnerLine_zpow_eq_one_of_three_dvd hv3 hJ
      have hyw : y' = wElt φ₂ ^ (a * i) := by rw [hydecomp, hvJ, one_mul]
      have hmem : y' ∈ Subgroup.zpowers x := by
        rw [h.zpowers_x, hyw]
        exact (Subgroup.mem_zpowers_iff).mpr ⟨a * i, rfl⟩
      exact hnotx hmem
    · have hmixed := ggHalfInnerLine_mixed hv3 hw3 hcomm_vw hI hJ hydecomp
      rcases hmixed with hmixed | hmixed
      · exact Or.inr ⟨1, Or.inl rfl, by simpa only [pow_one] using hmixed⟩
      · exact Or.inr ⟨2, Or.inr rfl, hmixed⟩

end GGHalfCtx

end CFSG.StandardType

end
