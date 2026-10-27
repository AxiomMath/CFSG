module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B1NCore
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aY2Fix
public import CFSG.RankThree.PartTwo.Sec21.CarterFF81aTauT1

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne.B1Normal

private theorem commute_of_mem_zpowers {M : Type*} [Group M] {a u z : M}
    (hu : a * u = u * a) (hz : z ∈ Subgroup.zpowers a) : z * u = u * z := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  rw [← hk]
  exact (show Commute a u from hu).zpow_left k

private theorem coprime_six_of_dvd_of_odd {m N : ℕ} (hdvd : m ∣ N) (hodd : Odd N)
    (h3 : ¬ 3 ∣ N) : Nat.Coprime m 6 := by
  have hm_odd : Odd m := Odd.of_dvd_nat hodd hdvd
  have hm3 : ¬ 3 ∣ m := fun h => h3 (h.trans hdvd)
  have h2 : Nat.Coprime m 2 := hm_odd.coprime_two_right
  have h3' : Nat.Coprime m 3 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
  have h6 : Nat.Coprime m (2 * 3) := Nat.coprime_mul_iff_right.mpr ⟨h2, h3'⟩
  simpa using h6

theorem y_fixes_z0 {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z)
    {Y : Subgroup (MulAut ↥(GGFF.Bt b z))} {sX tX : MulAut ↥(GGFF.Bt b z)}
    (hodd : Odd (Nat.card Y)) (h3 : ¬ 3 ∣ Nat.card Y)
    (htX : tX bG = bG ∧ tX (zsG 0) = (zsG 0)⁻¹ ∧ tX (zsG 1) = zsG 1 ∧ tX (zsG 2) = zsG 2)
    (hE : CFSG.RankThree.PartTwo.Sec21.FF79.IsElemAb 3 2
      (Subgroup.zpowers (bG : ↥(GGFF.Bt b z)) ⊔ Subgroup.zpowers (zsG 0)))
    (hker_E : (∀ x : ↥(GGFF.Bt b z), x⁻¹ * (sX * tX) x = 1 ↔
        x ∈ Subgroup.zpowers (bG : ↥(GGFF.Bt b z)) ⊔ Subgroup.zpowers (zsG 0)) ∨
      (∀ x : ↥(GGFF.Bt b z), x * (sX * tX) x = 1 ↔
        x ∈ Subgroup.zpowers (bG : ↥(GGFF.Bt b z)) ⊔ Subgroup.zpowers (zsG 0)))
    (hdec : ∀ y ∈ Y, ∃ a ∈ Y, ∃ c ∈ Y,
      a * (sX * tX) = (sX * tX) * a ∧ c * tX = tX * c ∧ y = a * c) :
    ∀ y ∈ Y, y (zsG 0) = zsG 0 := by
  intro y hy
  obtain ⟨a, haY, c, hcY, hacomm, hccomm, hy_eq⟩ := hdec y hy
  let E : Subgroup ↥(GGFF.Bt b z) :=
    Subgroup.zpowers (bG : ↥(GGFF.Bt b z)) ⊔ Subgroup.zpowers (zsG 0)
  have hEA : IsElementaryAbelian 3 E := hE.1
  have hzs0E : (zsG 0 : ↥(GGFF.Bt b z)) ∈ E :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers (zsG 0))
  have hbGE : (bG : ↥(GGFF.Bt b z)) ∈ E :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers (bG : ↥(GGFF.Bt b z)))
  have ha_fix : ∀ v : ↥(GGFF.Bt b z), v ∈ E → a v = v := by
    have hdvd : Nat.card (Subgroup.zpowers a) ∣ Nat.card Y :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr haY)
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers a)) 6 :=
      coprime_six_of_dvd_of_odd hdvd hodd h3
    have hpres : ∀ z : MulAut ↥(GGFF.Bt b z), z ∈ Subgroup.zpowers a →
        Subgroup.map z E = E := by
      intro z hz
      rcases hker_E with hker | hker
      · exact map_kernel_inv_mul (commute_of_mem_zpowers hacomm hz) hker
      · exact map_kernel_mul (commute_of_mem_zpowers hacomm hz) hker
    have hres := CFSG.MulAut.act_trivial_of_preserves_card_nine
      (Y := Subgroup.zpowers a) hcop hE hpres
    exact fun v hv => hres a (Subgroup.mem_zpowers a) v hv
  have hc_fix : c (zsG 0) = zsG 0 := by
    have hdvd : Nat.card (Subgroup.zpowers c) ∣ Nat.card Y :=
      Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hcY)
    have hodd_c : Odd (Nat.card (Subgroup.zpowers c)) := Odd.of_dvd_nat hodd hdvd
    have hcomm_c : ∀ z : MulAut ↥(GGFF.Bt b z), z ∈ Subgroup.zpowers c →
        z * tX = tX * z := fun z hz => commute_of_mem_zpowers hccomm hz
    have hB : GGFF.Bt b z = (Subgroup.zpowers b ⊔
        (Subgroup.zpowers (GGFF.zs z 1) ⊔ Subgroup.zpowers (GGFF.zs z 2))) ⊔
        Subgroup.zpowers (GGFF.zs z 0) := by
      rw [GGFF.SettingCore.Bt_eq_closure b z]
      rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
      simp only [← Subgroup.closure_union]
      congr 1
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
      tauto
    obtain ⟨himage, hcover⟩ :=
      CFSG.RankThree.PartTwo.Sec21.FF81.FF81Hyp.commutator_t1 hB (isElemAb_Bt h)
        (GGFF.SettingCore.b_mem_Bt b z) (GGFF.SettingCore.zs_mem_Bt b z 0)
        (GGFF.SettingCore.zs_mem_Bt b z 1) (GGFF.SettingCore.zs_mem_Bt b z 2)
        htX.1 htX.2.1 htX.2.2.1 htX.2.2.2
    have hbG_pow : (bG : ↥(GGFF.Bt b z)) ^ 3 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (bG : ↥(GGFF.Bt b z)) hbGE
    have hbG_le : orderOf (bG : ↥(GGFF.Bt b z)) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr hbG_pow)
    have hz0_ne : (zsG 0 : ↥(GGFF.Bt b z)) ≠ 1 := by
      intro h1
      have hEeq : E = Subgroup.zpowers (bG : ↥(GGFF.Bt b z)) := by
        change Subgroup.zpowers (bG : ↥(GGFF.Bt b z)) ⊔
          Subgroup.zpowers (zsG 0 : ↥(GGFF.Bt b z)) =
          Subgroup.zpowers (bG : ↥(GGFF.Bt b z))
        rw [h1, Subgroup.zpowers_one_eq_bot, sup_bot_eq]
      have h9E : Nat.card E = 9 := by
        have h := hE.2
        rw [show (3 : ℕ) ^ 2 = 9 by norm_num] at h
        exact h
      have h9 : Nat.card (Subgroup.zpowers (bG : ↥(GGFF.Bt b z))) = 9 := by
        rw [← hEeq]
        exact h9E
      rw [Nat.card_zpowers] at h9
      omega
    have hz0_pow : (zsG 0 : ↥(GGFF.Bt b z)) ^ 3 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (zsG 0) hzs0E
    have hcard : Nat.card (Subgroup.zpowers (zsG 0 : ↥(GGFF.Bt b z))) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hz0_pow hz0_ne
    have hres := CFSG.MulAut.eq_on_zpowers_of_commute_card_three
      (Y₂ := Subgroup.zpowers c) (t := tX) (b₁ := (zsG 0 : ↥(GGFF.Bt b z)))
      hodd_c hcard hcomm_c himage hcover
    exact hres c (Subgroup.mem_zpowers c)
  calc y (zsG 0) = (a * c) (zsG 0) := by rw [hy_eq]
    _ = a (c (zsG 0)) := MulAut.mul_apply ↥(GGFF.Bt b z) a c (zsG 0)
    _ = a (zsG 0) := by rw [hc_fix]
    _ = zsG 0 := ha_fix (zsG 0) hzs0E

end CFSG.StandardType.FF81.PropOne.B1Normal

end
