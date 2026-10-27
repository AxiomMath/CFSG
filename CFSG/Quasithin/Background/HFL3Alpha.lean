module

public import CFSG.Quasithin.Background.HFL3Out
public import CFSG.Quasithin.Background.HFL3Three

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag SU3
  Tri

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem sq_eq_one_HMod (X : HMod n K) : X ^ 2 = 1 :=
  mat_injective (by rw [sq, mat_mul, mat_one, CharTwo.add_self_eq_zero])

theorem card_le_two_mul_inf (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hA : A ≤ norm hK) (hAe : IsElemAbelian2 A) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ linImg hK) := by
  classical
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  by_cases hL : A ≤ linImg hK
  · rw [inf_eq_left.mpr hL]
    omega
  obtain ⟨a, ha, haL⟩ := IsConcreteLE.not_le_iff_exists.mp hL
  have hinv : ∀ b ∈ A, b * b = 1 := fun b hb => by rw [← sq]; exact hAe.2 b hb
  have hout : ∀ b ∈ A, b ∉ linImg hK → ∃ B : GL (Fin 3) K, b = rhoT hK B * fldAut (bar n) := by
    intro b hb hbL
    obtain ⟨B, h | h⟩ := exists_of_involution hn hK (hA hb) (hinv b hb)
    · exact absurd ⟨B, h.symm⟩ hbL
    · exact ⟨B, h⟩
  have hbar2 : (bar n : K ≃+* K) * bar n = 1 := by
    ext x
    exact bar_bar hK x
  have hprod : ∀ b ∈ A, b ∉ linImg hK → a * b ∈ linImg hK := by
    intro b hb hbL
    obtain ⟨B, hB⟩ := hout a ha haL
    obtain ⟨B', hB'⟩ := hout b hb hbL
    refine ⟨B * mapGL (bar n) B', ?_⟩
    rw [hB, hB', map_mul, mul_assoc (rhoT hK B), ← mul_assoc (fldAut (bar n)),
      fldAut_mul_rhoT hK, mul_assoc (rhoT hK (mapGL (bar n) B')), ← fldAut_mul, hbar2,
      fldAut_one, mul_one]
  let f : ↥A → Bool × ↥(A ⊓ linImg hK) := fun b =>
    if hb : (b : MulAut (HMod n K)) ∈ linImg hK then (true, ⟨b, b.2, hb⟩)
    else (false, ⟨a * b, A.mul_mem ha b.2, hprod b b.2 hb⟩)
  have hf : Function.Injective f := by
    intro b c h
    simp only [f] at h
    split_ifs at h with hb hc hc
    · exact Subtype.ext (congrArg (fun p => (p.2 : MulAut (HMod n K))) h)
    · exact absurd (congrArg Prod.fst h) (by simp)
    · exact absurd (congrArg Prod.fst h) (by simp)
    · exact Subtype.ext (mul_left_cancel (congrArg (fun p => (p.2 : MulAut (HMod n K))) h))
  have h1 := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h1

theorem card_fixV_le_of_three (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hA : A ≤ norm hK) (hAe : IsElemAbelian2 A)
    (hcard : 2 ^ (3 * n) ≤ Nat.card A ∨ (A ≤ img hK ∧ 2 ^ n < Nat.card A)) :
    Nat.card (fixV A) ≤ 2 ^ (4 * n) := by
  rcases hcard with h3 | ⟨hAL, h1⟩
  · set A₀ := A ⊓ linImg hK with hA₀
    have h2 : Nat.card A ≤ 2 * Nat.card A₀ := card_le_two_mul_inf hn hK hA hAe
    have hA₀e : IsElemAbelian2 A₀ := ⟨fun a ha b hb => hAe.1 a ha.1 b hb.1,
      fun a ha => hAe.2 a ha.1⟩
    have hA₀L : A₀ ≤ img hK := le_img_of_isPGroup hK inf_le_right fun x => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (hA₀e.2 x x.2)⟩
    have hlt : 2 ^ n < Nat.card A₀ := by
      have h4 : 2 ^ (3 * n) = 2 * 2 ^ (3 * n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have h5 : 2 ^ n < 2 ^ (3 * n - 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    calc Nat.card (fixV A) ≤ Nat.card (fixV A₀) :=
          Subgroup.card_le_of_le fun v hv a ha => hv a ha.1
      _ ≤ 2 ^ (4 * n) := card_fixV_le_of_card_gt hn hK hA₀L hA₀e hlt
  · exact card_fixV_le_of_card_gt hn hK hAL hAe h1

theorem card_le_of_elemAb_norm (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {E : Subgroup (MulAut (HMod n K))} (hE : E ≤ norm hK) (hEe : IsElemAbelian2 E) :
    Nat.card E ≤ 2 ^ (4 * n) := by
  have hK4 : Nat.card K ^ 2 = 2 ^ (4 * n) := by rw [hK, ← pow_mul, ← pow_mul]; ring_nf
  by_cases hL : E ≤ linImg hK
  · exact (card_le_of_elemAb hK hL hEe).trans hK4.le
  · obtain ⟨a, ha, haL⟩ := IsConcreteLE.not_le_iff_exists.mp hL
    have h := card_le_of_not_le_linImg hn hK hE hEe ha haL
    rw [hK, ← pow_mul, ← pow_succ'] at h
    exact h.trans (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem le_rkIdx_of_card_mul_le' {W : Type*} [CommGroup W] [Finite W] (hexp : ∀ v : W, v ^ 2 = 1)
    (H : Subgroup W) {k : ℕ} (h : Nat.card H * 2 ^ k ≤ Nat.card W) : k ≤ rkIdx H := by
  have h1 : Nat.card H = 2 ^ rk H := card_eq_two_pow hexp H
  have h2 : Nat.card W = 2 ^ rk W :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hexp)
  have h3 := rk_add_rkIdx H
  rw [h1, h2, ← pow_add, ← h3] at h
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  omega

theorem le_rkIdx_of_odd (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {y : MulAut (HMod n K)} (hy : y ∈ norm hK) (hy1 : y ≠ 1) (hodd : Odd (orderOf y)) :
    4 * n ≤ rkIdx (fixV (Subgroup.zpowers y)) := by
  refine le_rkIdx_of_card_mul_le' sq_eq_one_HMod _ ?_
  rw [card_HMod hn hK]
  calc Nat.card ↥(fixV (Subgroup.zpowers y)) * 2 ^ (4 * n) ≤ 2 ^ (5 * n) * 2 ^ (4 * n) :=
        Nat.mul_le_mul_right _ (card_fixV_odd_le hn hK hy hy1 hodd).1
    _ = 2 ^ (9 * n) := by rw [← pow_add]; ring_nf

theorem rkIdx_anti {W : Type*} [Group W] [Finite W] {U U' : Subgroup W} (h : U ≤ U') :
    rkIdx U' ≤ rkIdx U := by
  unfold rkIdx
  exact padicValNat_two_le_of_dvd Subgroup.index_ne_zero_of_finite (Subgroup.index_dvd_of_le h)

theorem le_rkIdx_of_card_le (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {U : Subgroup (HMod n K)}
    {j : ℕ} (hj : j ≤ 9 * n) (h : Nat.card U ≤ 2 ^ j) : 9 * n - j ≤ rkIdx U := by
  refine le_rkIdx_of_card_mul_le' sq_eq_one_HMod _ ?_
  rw [card_HMod hn hK]
  calc Nat.card U * 2 ^ (9 * n - j) ≤ 2 ^ j * 2 ^ (9 * n - j) := Nat.mul_le_mul_right _ h
    _ = 2 ^ (9 * n) := by rw [← pow_add]; congr 1; omega

theorem alphaSet_spec (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hM : M ≤ norm hK) {k : ℕ} (hk : k ∈ alphaSet M) :
    n = 1 ∧ 5 ≤ k := by
  classical
  have : Finite (MulAut (HMod n K)) := MulEquiv.finite_left
  obtain ⟨hk2, U, -, hUk, hkle⟩ := hk
  obtain ⟨E, hEM, hE, hEc⟩ := exists_isElemAbelian_card_pRank (M ⊓ centSub U)
  have hE2 : IsElemAbelian2 E := isElemAbelian2_iff.2 hE
  have hEN : E ≤ norm hK := hEM.trans (inf_le_left.trans hM)
  set m := CFSG.Open.pRank 2 (M ⊓ centSub U) with hm
  have hUE : U ≤ fixV E := fun u hu x hx => mem_centSub.mp (hEM hx).2 u hu
  have hle : rkIdx (fixV E) ≤ k := hUk ▸ rkIdx_anti hUE
  have hV := card_HMod hn hK
  have hm4 : m ≤ 4 * n := by
    have h := card_le_of_elemAb_norm hn hK hEN hE2
    rw [hEc] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
  have hfixle : ∀ r ∈ E, fixV E ≤ fixV (Subgroup.zpowers r) := fun r hr v hv =>
    mem_fixV_zpowers_iff.mpr (hv r hr)
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  ·
    have hm1 : m = 1 := by omega
    obtain ⟨t, htE, ht1⟩ : ∃ t ∈ E, t ≠ 1 := by
      by_contra h
      push Not at h
      rw [(Subgroup.eq_bot_iff_forall E).2 h, Subgroup.card_bot, hm1] at hEc
      norm_num at hEc
    have htt : t * t = 1 := by rw [← sq]; exact hE2.2 t htE
    have h1 := card_fixV_le_of_involution hn hK (hEN htE) htt ht1
    have h2 := le_rkIdx_of_card_le hn hK (by omega)
      ((Subgroup.card_le_of_le (hfixle t htE)).trans h1)
    omega
  ·
    have h2 := card_le_two_mul_inf hn hK hEN hE2
    rw [hEc] at h2
    obtain ⟨r, hrE, hr1⟩ : ∃ r ∈ E ⊓ linImg hK, r ≠ 1 := by
      by_contra h
      push Not at h
      rw [(Subgroup.eq_bot_iff_forall _).2 h, Subgroup.card_bot] at h2
      have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      omega
    obtain ⟨A, hA⟩ := hrE.2
    have hr5 : Nat.card ↥(fixV (Subgroup.zpowers r)) ≤ 2 ^ (5 * n) := by
      rw [← hA] at hr1 ⊢
      exact card_fixV_rhoT_le hn hK hr1
    have hE5 : Nat.card ↥(fixV E) ≤ 2 ^ (5 * n) :=
      (Subgroup.card_le_of_le (hfixle _ hrE.1)).trans hr5
    have h4 := le_rkIdx_of_card_le hn hK (by omega) hE5
    by_cases hm3 : 3 * n ≤ m
    · have hc3 : 2 ^ (3 * n) ≤ Nat.card E := by
        rw [hEc]
        exact Nat.pow_le_pow_right (by norm_num) hm3
      have h5 := card_fixV_le_of_three hn hK hEN hE2 (Or.inl hc3)
      have h6 := le_rkIdx_of_card_le hn hK (by omega) h5
      omega
    · omega

end CFSG.Quasithin.H.L3Nine
