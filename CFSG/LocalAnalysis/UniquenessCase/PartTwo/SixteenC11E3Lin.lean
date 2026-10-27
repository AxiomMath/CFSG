module

public import CFSG.GroupTheory.BinaryFixedFreeRank
public import CFSG.Quasithin.Background.InvolutionQuadratic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsNoInv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

private lemma s1611e3_commute_zpowers {V : Type} [CommGroup V] {g i : MulAut V}
    (hgi : g * i = i * g) {y : MulAut V} (hy : y ∈ Subgroup.zpowers i) :
    g * y = y * g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (show Commute g i from hgi).zpow_right n

private lemma s1611e3_apply_commSub_zpowers_mem {V : Type} [CommGroup V] {g i : MulAut V}
    (hgi : g * i = i * g) {w : V}
    (hw : w ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers i)) :
    g w ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers i) := by
  refine Subgroup.closure_induction (p := fun c _ =>
      g c ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers i)) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨y, hy, u, -, rfl⟩
    have hyg : g * y = y * g := s1611e3_commute_zpowers hgi hy
    have h1 : g (y u) = y (g u) := by rw [← MulAut.mul_apply, hyg, MulAut.mul_apply]
    rw [map_mul, map_inv, h1]
    exact Subgroup.subset_closure ⟨y, hy, g u, Subgroup.mem_top _, rfl⟩
  · rw [map_one]; exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    rw [map_inv]; exact Subgroup.inv_mem _ ha

theorem s1611e3_comm_of_normalizes_of_odd {V : Type} [CommGroup V] [Finite V]
    (h2 : ∀ v : V, v ^ 2 = 1) (hodd : Odd (rk V)) {z t : MulAut V} (hz : orderOf z = 7)
    (hfix : ∀ v : V, z v = v → v = 1) (ht : orderOf t = 2)
    (hn : t * z * t⁻¹ ∈ Subgroup.zpowers z) : t * z = z * t := by
  classical
  have hz7 : z ^ 7 = 1 := by simpa [hz] using pow_orderOf_eq_one z
  have ht21 : t ^ (2 ^ 1) = 1 := by
    rw [show (2 : ℕ) ^ 1 = 2 by norm_num]
    simpa [ht] using pow_orderOf_eq_one t
  rcases s16t_a_conj_eq_or_inv hz7 hn ht21 with h | h
  · exact mul_inv_eq_iff_eq_mul.mp h
  · exact (s16t_a_false_of_inverted h2 hodd hz7 hfix h).elim

theorem s1611e3_three_le_rkIdx_of_normalizes {V : Type} [CommGroup V] [Finite V]
    (h2 : ∀ v : V, v ^ 2 = 1) (h6 : 6 ≤ rk V) {z t : MulAut V} (hz : orderOf z = 7)
    (hfix : ∀ v : V, z v = v → v = 1) (ht : orderOf t = 2)
    (hn : t * z * t⁻¹ ∈ Subgroup.zpowers z) : 3 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  classical
  have hz7 : z ^ 7 = 1 := by simpa [hz] using pow_orderOf_eq_one z
  have ht2 : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
  have ht21 : t ^ (2 ^ 1) = 1 := by
    rw [show (2 : ℕ) ^ 1 = 2 by norm_num]
    exact ht2
  have hii : t * t = 1 := by rw [← pow_two]; exact ht2
  have ht_inv : t⁻¹ = t := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two]
    exact ht2
  have ht_ne_one : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht
    exact (by norm_num : (1 : ℕ) ≠ 2) ht
  rw [rkIdx_fixV_zpowers t, commV_eq_commSub]
  rcases s16t_a_conj_eq_or_inv hz7 hn ht21 with hcomm | hinv
  ·
    have hzt_comm : z * t = t * z := (mul_inv_eq_iff_eq_mul.mp hcomm).symm
    have hzi_comm : z⁻¹ * t = t * z⁻¹ := by
      have h := congrArg Inv.inv hzt_comm
      rw [mul_inv_rev, mul_inv_rev, ht_inv] at h
      exact h.symm
    have hne : commSub (⊤ : Subgroup V) (Subgroup.zpowers t) ≠ ⊥ := by
      intro hbot
      have hle : (⊤ : Subgroup V) ≤ fixV (Subgroup.zpowers t) := commSub_eq_bot_iff.mp hbot
      apply ht_ne_one
      ext w
      have hw : w ∈ fixV (Subgroup.zpowers t) := hle (Subgroup.mem_top w)
      rwa [mem_fixV_zpowers_iff] at hw
    have hrkpos : 0 < rk ↥(commSub (⊤ : Subgroup V) (Subgroup.zpowers t)) :=
      Nat.pos_of_ne_zero (fun h0 => hne ((rk_eq_zero_iff h2).mp h0))
    have hfixx : fixV (Subgroup.zpowers z) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro v hv
      rw [mem_fixV_zpowers_iff] at hv
      exact hfix v hv
    have hfixU : commSub (⊤ : Subgroup V) (Subgroup.zpowers t) ⊓
        fixV (Subgroup.zpowers z) = ⊥ := by
      rw [hfixx, inf_bot_eq]
    have hW_inv : ∀ y ∈ Subgroup.zpowers z, ∀ w ∈ commSub (⊤ : Subgroup V)
        (Subgroup.zpowers t), y w ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers t) := by
      intro y hy w hw
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (zpow_induction_right (g := z) (P := fun y => ∀ w ∈
          commSub (⊤ : Subgroup V) (Subgroup.zpowers t), y w ∈
          commSub (⊤ : Subgroup V) (Subgroup.zpowers t))
        (fun w hw => by simpa using hw)
        (fun a ha w hw => by
          rw [MulAut.mul_apply]
          exact ha (z w) (s1611e3_apply_commSub_zpowers_mem hzt_comm (w := w) hw))
        (fun a ha w hw => by
          rw [MulAut.mul_apply]
          exact ha (z⁻¹ w) (s1611e3_apply_commSub_zpowers_mem hzi_comm (w := w) hw))
        n) w hw
    have horder2 : orderOf (2 : ZMod 7) = 3 := by
      have h1 : (2 : ZMod 7) ^ 3 = 1 := by decide
      have h2m : ∀ m, m < 3 → 0 < m → (2 : ZMod 7) ^ m ≠ 1 := by
        intro m hm3 hm0
        interval_cases m <;> decide
      exact (orderOf_eq_iff (n := 3) (by norm_num)).mpr ⟨h1, h2m⟩
    have hY : IsPGroup 7 ↥(Subgroup.zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz]; norm_num)
    have hdvd3 : 3 ∣ rk ↥(commSub (⊤ : Subgroup V) (Subgroup.zpowers t)) := by
      haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      have hdvd := CFSG.GroupTheory.orderOf_two_dvd_rk_of_inf_fixV_eq_bot (V := V) (p := 7)
        h2 (Y := Subgroup.zpowers z) hY hW_inv hfixU
      rwa [horder2] at hdvd
    exact Nat.le_of_dvd hrkpos hdvd3
  ·
    have htz : t * z = z⁻¹ * t := by
      have h := congrArg (fun y : MulAut V => y * t) hinv
      rw [mul_assoc, inv_mul_cancel, mul_one] at h
      exact h
    have hzt : z = t * z⁻¹ * t := by
      have h := congrArg (fun y : MulAut V => t * y) htz
      rw [← mul_assoc, hii, one_mul] at h
      rwa [← mul_assoc] at h
    let j : MulAut V := z * t
    have hj2 : j * j = 1 := by
      show (z * t) * (z * t) = 1
      calc (z * t) * (z * t) = z * (t * z) * t := by group
        _ = z * (z⁻¹ * t) * t := by rw [htz]
        _ = (z * z⁻¹) * (t * t) := by group
        _ = 1 := by rw [mul_inv_cancel, hii, mul_one]
    have hj2' : j ^ 2 = 1 := by rw [pow_two]; exact hj2
    have hjt : j * t = z := by
      show (z * t) * t = z
      rw [mul_assoc, hii, mul_one]
    have hdisj : fixV (Subgroup.zpowers t) ⊓ fixV (Subgroup.zpowers j) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro v hv
      rw [Subgroup.mem_inf, mem_fixV_zpowers_iff, mem_fixV_zpowers_iff] at hv
      obtain ⟨hvt, hvj⟩ := hv
      have hzv : z v = v := by
        have h1 : (j * t) v = v := by rw [MulAut.mul_apply, hvt, hvj]
        rwa [hjt] at h1
      exact hfix v hzv
    have hsum := rk_sup_add_rk_inf (fixV (Subgroup.zpowers t)) (fixV (Subgroup.zpowers j))
    rw [hdisj, rk_bot, add_zero] at hsum
    have hle : rk ↥(fixV (Subgroup.zpowers t) ⊔ fixV (Subgroup.zpowers j)) ≤ rk V := by
      have hp := rk_mono (H := fixV (Subgroup.zpowers t) ⊔ fixV (Subgroup.zpowers j))
        (K := (⊤ : Subgroup V)) le_top
      rwa [rk_top] at hp
    have hCiCj : rk ↥(fixV (Subgroup.zpowers t)) + rk ↥(fixV (Subgroup.zpowers j)) ≤ rk V := by
      rw [← hsum]; exact hle
    have hki := rk_commSub_add_rk_inf_fixV (V := V) (g := t) (W := (⊤ : Subgroup V))
      (fun _ _ _ _ => Subgroup.mem_top _)
    rw [top_inf_eq, rk_top] at hki
    have hkj := rk_commSub_add_rk_inf_fixV (V := V) (g := j) (W := (⊤ : Subgroup V))
      (fun _ _ _ _ => Subgroup.mem_top _)
    rw [top_inf_eq, rk_top] at hkj
    have hki_le : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ rk ↥(fixV (Subgroup.zpowers t)) :=
      rk_mono (by
        have h := commV_zpowers_le_fixV_of_involution h2 ht2
        rwa [commV_eq_commSub] at h)
    have hkj_le : rk ↥(commSub ⊤ (Subgroup.zpowers j)) ≤ rk ↥(fixV (Subgroup.zpowers j)) :=
      rk_mono (by
        have h := commV_zpowers_le_fixV_of_involution h2 hj2'
        rwa [commV_eq_commSub] at h)
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
