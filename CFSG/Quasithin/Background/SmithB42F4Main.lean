module

public import CFSG.Quasithin.Background.SmithB42F4Pure
public import CFSG.Quasithin.Background.SmithB42F4Lang
public import CFSG.Quasithin.Background.SmithB42Disp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel

public section

namespace CFSG.Quasithin.B42F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Quasithin.B42Disp
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form mem_inner_of_sq_eq_one_of_odd)

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

omit [Finite K]
  [CharP K F4.prime] in
theorem card_le_two_pow_pred {E : Type*} [Group E] [Finite E] (hE : ∀ x : E, x ^ 2 = 1)
    {n : ℕ} (hlt : Nat.card E < 2 ^ n) : Nat.card E ≤ 2 ^ (n - 1) := by
  have := Fact.mk Nat.prime_two
  have hp : IsPGroup 2 E := fun x => ⟨1, by rw [pow_one]; exact hE x⟩
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk] at hlt ⊢
  have hkn : k < n := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hlt
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

omit [Finite K] in
theorem sylowL_mul_self (l : K) : sylowL a K l * sylowL a K l = 1 := by
  have h := (sylowV_zero_zero_sq_eq_one_iff (m := a) (K := K) 0 0 0 0 0 0 0 0 0 l).2
    ⟨rfl, rfl, rfl, rfl, zero_mul _⟩
  rw [sylowV_eq_blocks_of_e, sylowF_zero_zero, sylowH_zero_zero, sylowJ_zero, sylowK_zero,
    one_mul, one_mul, one_mul, one_mul, sq] at h
  exact h

theorem exists_tOne_eq_conj_mul_conj (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ p₁ ∈ F4.reeGamma K a, ∃ p₂ ∈ F4.reeGamma K a,
      sylowL a K 1 = p₁ * sylowH a K 0 1 * p₁⁻¹ * (p₂ * sylowH a K 0 1 * p₂⁻¹) := by
  have hBU : sylowB a K 1 0 ∈ F4.reeGamma K a :=
    reeFixedPosUnipotent_le_reeGamma' (reeFixedOrbitUnipotent_le _ (sylowB_mem_U2 hK 1 0))
  have hAU : sylowA a K 1 ∈ F4.reeGamma K a :=
    reeFixedPosUnipotent_le_reeGamma' (reeFixedOrbitUnipotent_le _ (sylowA_mem_U1 hK 1))
  set w := sylowB a K 1 0 * weylTwo K * sylowB a K 1 0 * sylowA a K 1 * weylOne K with hw
  have hwΓ : w ∈ F4.reeGamma K a :=
    mul_mem (mul_mem (mul_mem (mul_mem hBU weylTwo_mem) hBU) hAU) weylOne_mem
  set n := weylOne K * weylTwo K * weylOne K with hn
  have hnΓ : n ∈ F4.reeGamma K a := mul_mem (mul_mem weylOne_mem weylTwo_mem) weylOne_mem
  have hB : sylowB a K 0 1 = n⁻¹ * sylowH a K 0 1 * n⁻¹⁻¹ := by
    rw [← weyl_conj_sylowB_zero (m := a) (c := (1 : K)), ← hn]
    group
  refine ⟨w * n⁻¹, mul_mem hwΓ (inv_mem hnΓ), w, hwΓ, ?_⟩
  rw [← fusion_word (m := a) (K := K), ← hw, hB]
  group

theorem dispCriterion_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    DispCriterion (F4.reeGamma K a) := by
  have := finite_modGL (τ := F4.tag) (K := K)
  set f := 2 * a + 1 with hf
  have hq6 : (2 ^ f) ^ 6 = 2 ^ (6 * f) := by rw [← pow_mul, mul_comm]
  have hq3 : (2 ^ f) ^ 3 = 2 ^ (3 * f) := by rw [← pow_mul, mul_comm]
  have hZ : Subgroup.center (F4.reeGamma K a) = ⊥ := large_Ree_fixed_group_center_trivial a K hK
  obtain ⟨ℓ, hℓ, hℓ2, hord⟩ := exists_prime_orderOf_two_eq (12 * f) (by omega) (by omega)
  obtain ⟨c, hcΓ, hcord, hinv⟩ := exists_inverted_by_tOne ha hK hℓ hℓ2 hord
  have hodd : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (F4.reeGamma K a))) := by
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      large_Ree_full_inner_field_automorphism_normal_form a ha K hK
    rw [hcard]
    exact ⟨a, rfl⟩
  have hinner : ∀ α : MulAut (F4.reeGamma K a), α * α = 1 →
      α ∈ (MulAut.conj : F4.reeGamma K a →* MulAut (F4.reeGamma K a)).range := fun α hα =>
    mem_inner_of_sq_eq_one_of_odd hodd
      (by rw [sq]; exact hα)
  refine dispCriterion_of_classes hZ (fun ξ => IsTConj a K (ξ : ModGL F4.tag K)) (6 * f - 1)
    (3 * f - 1) 0 ?_ ?_ ?_ ?_ ?_ ?_
  ·
    intro E hE
    have hlt := card_lt_of_isElem2 ha hK hE.1 hE.2
    rw [hq6] at hlt
    exact card_le_two_pow_pred (fun x => Subtype.ext (hE.2 _ x.2)) hlt
  ·
    intro E hE hpure
    have hlt := card_lt_of_pureZ ha hK hE.1 hE.2 (fun g hg hg1 => by
      have hg1' : (g : ModGL F4.tag K) ≠ 1 := fun h => hg1 (Subtype.ext h)
      have hsq : (g : ModGL F4.tag K) ^ 2 = 1 := by
        rw [← Subgroup.coe_pow, hE.2 g hg, Subgroup.coe_one]
      rcases isZConj_or_isTConj ha hK g.2 hsq hg1' with hz | ht
      · exact hz
      · exact absurd ht (hpure g hg hg1))
    rw [hq3] at hlt
    exact card_le_two_pow_pred (fun x => Subtype.ext (hE.2 _ x.2)) hlt
  ·
    intro F hF
    have hle : F ≤ (MulAut.conj : F4.reeGamma K a →* MulAut (F4.reeGamma K a)).range :=
      fun α hα => hinner α (by rw [← sq]; exact hF.2 α hα)
    rw [inf_eq_left.2 hle, pow_zero, one_mul]
  ·
    intro ξ hξ2 hξ1 hξB
    obtain ⟨g, hg, hgξ⟩ := hξB
    set c' : F4.reeGamma K a := ⟨g⁻¹ * c * g, mul_mem (mul_mem (inv_mem hg) hcΓ) hg⟩ with hc'
    refine Or.inl (dispAt_of_inverts hZ (α := MulAut.conj ξ) (c := c') ?_ ?_ hℓ hℓ2 ?_ ?_)
    · rw [← map_mul, hξ2, map_one]
    · rw [MulAut.conj_apply]
      refine Subtype.ext ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc']
      have hξ : (ξ : ModGL F4.tag K) = g⁻¹ * sylowL a K 1 * g := by rw [← hgξ]; group
      rw [hξ]
      calc g⁻¹ * sylowL a K 1 * g * (g⁻¹ * c * g) * (g⁻¹ * sylowL a K 1 * g)⁻¹ =
          g⁻¹ * (sylowL a K 1 * c * (sylowL a K 1)⁻¹) * g := by group
        _ = (g⁻¹ * c * g)⁻¹ := by rw [hinv]; group
    · have : orderOf c' = ℓ := by
        rw [← Subgroup.orderOf_coe, hc']
        change orderOf (g⁻¹ * c * g) = ℓ
        rw [show g⁻¹ * c * g = MulAut.conj g⁻¹ c by simp,
          MulEquiv.orderOf_eq, hcord]
      rw [this]
    · rw [add_zero, ← pow_mul, hord]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  ·
    intro α hα hαO
    exact absurd (hinner α hα) hαO
  ·
    intro E hE1 hE hpure
    obtain ⟨⟨ξ, hξE⟩, hξ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE1
    have hξ1' : ξ ≠ 1 := fun h => hξ1 (Subtype.ext h)
    have hξ1'' : (ξ : ModGL F4.tag K) ≠ 1 := fun h => hξ1' (Subtype.ext h)
    have hsq : (ξ : ModGL F4.tag K) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, hE.2 ξ hξE, Subgroup.coe_one]
    have hz : IsZConj a K (ξ : ModGL F4.tag K) := by
      rcases isZConj_or_isTConj ha hK ξ.2 hsq hξ1'' with hz | ht
      · exact hz
      · exact absurd ht (hpure ξ hξE hξ1')
    obtain ⟨g, hg, hgξ⟩ := hz
    obtain ⟨p₁, hp₁, p₂, hp₂, ht⟩ := exists_tOne_eq_conj_mul_conj (a := a) hK
    refine Or.inl ⟨ξ, hξE, hξ1', Or.inl ?_⟩
    have hξ : (ξ : ModGL F4.tag K) = g⁻¹ * sylowH a K 0 1 * g := by rw [← hgξ]; group
    set m₁ : F4.reeGamma K a := ⟨p₁ * g, mul_mem hp₁ hg⟩ with hm₁
    set m₂ : F4.reeGamma K a := ⟨p₂ * g, mul_mem hp₂ hg⟩ with hm₂
    set cc : F4.reeGamma K a := ⟨c, hcΓ⟩ with hcc
    set T : F4.reeGamma K a := m₁ * ξ * m₁⁻¹ * (m₂ * ξ * m₂⁻¹) with hT
    have hTv : (T : ModGL F4.tag K) = sylowL a K 1 := by
      rw [hT]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hm₁, hm₂]
      rw [hξ, ht]
      group
    have key : ∀ T' : F4.reeGamma K a, (T' : ModGL F4.tag K) = sylowL a K 1 →
        T' * (cc * T' * cc⁻¹) = cc⁻¹ ^ 2 := by
      intro T' hT'
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_pow, Subgroup.coe_inv, hT']
      change sylowL a K 1 * (c * sylowL a K 1 * c⁻¹) = c⁻¹ ^ 2
      calc sylowL a K 1 * (c * sylowL a K 1 * c⁻¹) =
          (sylowL a K 1 * c * (sylowL a K 1)⁻¹) * (sylowL a K 1 * sylowL a K 1) * c⁻¹ := by
            group
        _ = c⁻¹ ^ 2 := by rw [hinv, sylowL_mul_self, mul_one, sq]
    have hTc := key T hTv
    have hprod : ([m₁, m₂, cc * m₁, cc * m₂].map fun m => m * ξ * m⁻¹).prod =
        T * (cc * T * cc⁻¹) := by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hT]
      group
    refine dispAt_conj hZ hℓ hℓ2 [m₁, m₂, cc * m₁, cc * m₂] ?_ ?_
    · rw [hprod, hTc]
      have hco : orderOf cc = ℓ := by rw [← Subgroup.orderOf_coe]; exact hcord
      rw [orderOf_pow' _ two_ne_zero, orderOf_inv, hco]
      have hcop : Nat.gcd ℓ 2 = 1 := (Nat.coprime_primes hℓ Nat.prime_two).2 hℓ2
      rw [hcop, Nat.div_one]
    · simp only [List.length_cons, List.length_nil]
      rw [← pow_mul, hord]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)

end CFSG.Quasithin.B42F4

namespace CFSG.Quasithin



theorem asB42ReeF4Large_holds :
    AsB42ReeF4Large := by
  refine B42Disp.asB42NoOffenderFor_of_dispCriterion fun X _ hX => ?_
  obtain ⟨f, -, -, hmodel⟩ := hX
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hmodel
  exact ⟨LieType.Ree.ReeTag.F4.reeGamma K a, inferInstance, ⟨e⟩,
    B42F4.dispCriterion_reeGamma ha (by rw [hK, hfa])⟩

end CFSG.Quasithin
