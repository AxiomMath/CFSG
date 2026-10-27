module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base15
public import CFSG.Quasithin.Vol2.Ch11SecBFacts36
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base14
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base8

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank K8

theorem factVMOffender_holds : FactVMOffender := by
  intro G _ _ L V W X T V₁ V₂ n h B hBT hBe hBa
  obtain ⟨K, _, _, _, hK, Φ, hL, hX⟩ :=
    exists_model_X h.elemW h.L_le_W h.two h.normalizer_le_W
  have hBN : B ≤ Subgroup.normalizer (W : Set G) := hBT.trans h.T_le_W
  obtain ⟨-, hc⟩ := offender_model h.two_le hK hX ((map_mem_aSet_iff Φ).mpr hBa)
  rw [card_map_autI, card_autI_eq_two_pow hBe hBN, hK, ← pow_mul] at hc
  have := Nat.pow_right_injective le_rfl hc
  omega

theorem factVMR2Pair_holds : FactVMR2Pair := by
  intro G _ _ L V W X T V₁ V₂ n h E hE hEe hmE hmW
  obtain ⟨K, _, _, _, hK, Φ, hL, hX⟩ :=
    exists_model_X h.elemW h.L_le_W h.two h.normalizer_le_W
  have hn := h.two_le
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hEN : E ≤ Subgroup.normalizer (W : Set G) := hE.trans inf_le_right
  set Â := (autI h.elemW E).map (congrHom Φ) with hÂ
  have hÂN : Â ≤ normD K :=
    (Subgroup.map_mono (autI_mono h.elemW (hE.trans inf_le_left))).trans hX
  have hÂe : IsElemAbelian2 Â :=
    (isElemAbelian2_map_congrHom Φ).mpr (isElemAbelian2_autI h.elemW hEe hEN)
  have hÂc : Nat.card Â = Nat.card K ^ 2 := by
    rw [hÂ, card_map_autI, card_autI_eq_two_pow hEe hEN, hmE, hK, ← pow_mul, mul_comm]
  have hfixc : Nat.card ↥(fixV Â) = Nat.card K ^ 4 := by
    rw [hÂ, ← comap_psi_inf_centralizer Φ hEN, card_comap_psi Φ inf_le_left]
    have h1 := two_pow_mQuot_mul_card Φ hK
      (inf_le_left : W ⊓ Subgroup.centralizer (E : Set G) ≤ W)
    rw [hmW, show 6 * n = 2 * n + 4 * n by ring, pow_add] at h1
    rw [Nat.eq_of_mul_eq_mul_left (by positivity) h1, hK, ← pow_mul, mul_comm]
  have hÂD : Â ≤ dgSub K := le_dgSub_of_card_fixV hÂN (by
    rw [hfixc]
    exact Nat.pow_lt_pow_right hq (by norm_num))
  obtain ⟨f, hf0, hkerf, hform, hsurj⟩ := axis_model hÂD hÂe hÂc hfixc
  have hker : Nat.card ↥(LinearMap.ker f) = Nat.card K ^ 2 := by
    have h1 := card_fixV_eq_sq hÂD
    rw [hfixc, hkerf, show Nat.card K ^ 4 = (Nat.card K ^ 2) ^ 2 by ring] at h1
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) h1).symm
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, f v₀ = 1 := by
    obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hf0 (LinearMap.ext hc)
    exact ⟨(f u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
  refine ⟨?_, ?_⟩
  · rw [commutator_eq_map Φ le_rfl hEN, comap_psi_self, commSub_top_axis hf0 hform hsurj,
      mQuot_bot_map_psi, card_sqSub, hker, hK, ← pow_mul, ← pow_mul,
      padicValNat.prime_pow]
    ring
  · obtain ⟨κ, hκ0, hκ1⟩ := exists_ne_zero_ne_one (K := K) (by
      rw [hK]
      calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
    set a' : W6 K := Multiplicative.ofAdd (Sum.elim v₀ (0 : Fin 3 → K)) with ha'
    set b' : W6 K := Multiplicative.ofAdd (Sum.elim (κ • v₀) (0 : Fin 3 → K)) with hb'
    have hcomm : ∀ (u : Fin 3 → K), f u ≠ 0 →
        ⁅Subgroup.zpowers (psi Φ (Multiplicative.ofAdd (Sum.elim u (0 : Fin 3 → K)))), E⁆ =
          (lineL (LinearMap.ker f)).map (psi Φ) := by
      intro u hu
      rw [commutator_eq_map Φ (Subgroup.zpowers_le.mpr (psi_mem Φ _)) hEN, comap_psi_zpowers,
        commSub_zpowers_axis hform hsurj hu]
    have hfa : f v₀ ≠ 0 := by rw [hv₀]; exact one_ne_zero
    have hfb : f (κ • v₀) ≠ 0 := by rw [map_smul, hv₀, smul_eq_mul, mul_one]; exact hκ0
    obtain ⟨w, hw, hw0⟩ := exists_mem_ker_ne_zero f
    refine ⟨psi Φ a', psi_mem Φ a', psi Φ b', psi_mem Φ b', ?_, by rw [hcomm _ hfa, hcomm _ hfb],
      ?_⟩
    · intro hC
      have hmem : a'⁻¹ * b' ∈ fixV Â := by
        rw [hÂ, ← comap_psi_inf_centralizer Φ hEN]
        refine ⟨psi_mem Φ _, ?_⟩
        change psi Φ (a'⁻¹ * b') ∈ Subgroup.centralizer (E : Set G)
        rw [map_mul, map_inv]
        exact hC
      obtain ⟨y, hy, hyw⟩ := hsurj w hw
      have h1 : toAddMap y (Multiplicative.toAdd (a'⁻¹ * b')) =
          Multiplicative.toAdd (a'⁻¹ * b') := congrArg Multiplicative.toAdd (hmem y hy)
      rw [hyw] at h1
      simp only [trvW, add_eq_left] at h1
      have h3 : f (Multiplicative.toAdd (a'⁻¹ * b') ∘ Sum.inl) • w = 0 := by
        funext j
        exact congrFun h1 (Sum.inl j)
      have h4 : Multiplicative.toAdd (a'⁻¹ * b') ∘ Sum.inl = (κ - 1) • v₀ := by
        rw [toAdd_mul, toAdd_inv, ha', hb', toAdd_ofAdd, toAdd_ofAdd, sub_smul, one_smul]
        funext j
        simp only [Function.comp_apply, Pi.add_apply, Pi.neg_apply, Sum.elim_inl, Pi.sub_apply]
        abel
      rw [h4, map_smul, hv₀, smul_eq_mul, mul_one] at h3
      rcases smul_eq_zero.mp h3 with h5 | h5
      · exact hκ1 (sub_eq_zero.mp h5)
      · exact hw0 h5
    · rw [hcomm _ hfa]
      exact (Subgroup.map_eq_bot_iff_of_injective _ (psi_injective Φ)).not.mpr
        (lineL_ne_bot hw hw0)

end CFSG.Quasithin.Vol2.Ch11.SecB
