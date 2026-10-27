module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613C3Conj
public import CFSG.Timmesfeld.Orders.ClassicalOmega

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.StandardType.D4Rank CFSG.StandardType.L613KG
  CFSG.Assembly.LowTwoRank

namespace L613C3

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_om8_int : (Nat.card (Om8 K) : ℤ) =
    (Nat.card K : ℤ) ^ 12 * ((Nat.card K : ℤ) ^ 4 - 1) *
      (((Nat.card K : ℤ) ^ 2 - 1) * ((Nat.card K : ℤ) ^ 4 - 1) * ((Nat.card K : ℤ) ^ 6 - 1)) := by
  rw [Nat.card_congr (projEquiv8 (K := K)).toEquiv, ← Nat.card_congr
    (coordinatePlusWitnessEquiv K
      (MulEquiv.refl (StatedProj (StatedOmega (StatedQuadPlus 4 K))))).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus (le_refl 4)]
  have hI : Finset.Icc 1 (4 - 1) = {1, 2, 3} := by decide
  rw [hI, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [show 4 * (4 - 1) = 12 from rfl, show 2 * 1 = 2 from rfl, show 2 * 2 = 4 from rfl,
    show 2 * 3 = 6 from rfl]
  ring

theorem card_om8_eq : Nat.card (Om8 K) = Nat.card K ^ 12 * (Nat.card K - 1) ^ 4 *
    (Nat.card K + 1) ^ 4 * (Nat.card K ^ 2 + 1) ^ 2 * (Nat.card K ^ 4 + Nat.card K ^ 2 + 1) := by
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  apply Nat.cast_injective (R := ℤ)
  rw [card_om8_int]
  push_cast [Nat.cast_sub hq1]
  ring

theorem card_om8_eq_three_pow {a r : ℕ} (hr : ¬ 3 ∣ r) (hq : Nat.card K - 1 = 3 ^ a * r)
    (ha : 1 ≤ a) : ∃ m, ¬ 3 ∣ m ∧ Nat.card (Om8 K) = 3 ^ (4 * a + 1) * m := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  obtain ⟨t, ht⟩ : 3 ∣ Nat.card K - 1 := by
    rw [hq]
    exact Dvd.dvd.mul_right (dvd_pow_self 3 (by omega)) r
  have hqt : Nat.card K = 3 * t + 1 := by omega
  set s := 1 + 3 * (2 * t + 7 * t ^ 2 + 12 * t ^ 3 + 9 * t ^ 4) with hs
  have hs4 : Nat.card K ^ 4 + Nat.card K ^ 2 + 1 = 3 * s := by
    rw [hqt, hs]
    ring
  refine ⟨Nat.card K ^ 12 * r ^ 4 * (Nat.card K + 1) ^ 4 * (Nat.card K ^ 2 + 1) ^ 2 * s, ?_, ?_⟩
  · have h1 : ¬ 3 ∣ Nat.card K := by omega
    have h2 : ¬ 3 ∣ Nat.card K + 1 := by omega
    have h3 : ¬ 3 ∣ Nat.card K ^ 2 + 1 := by
      have e : Nat.card K ^ 2 + 1 = 3 * (3 * t ^ 2 + 2 * t) + 2 := by
        rw [hqt]
        ring
      rw [e]
      intro h
      have := (Nat.dvd_add_right (dvd_mul_right 3 _)).mp h
      omega
    have h4 : ¬ 3 ∣ s := by
      rw [hs]
      intro h
      have := (Nat.dvd_add_left (dvd_mul_right 3 _)).mp h
      omega
    intro h
    simp only [hp.dvd_mul] at h
    rcases h with (((h | h) | h) | h) | h
    · exact h1 (hp.dvd_of_dvd_pow h)
    · exact hr (hp.dvd_of_dvd_pow h)
    · exact h2 (hp.dvd_of_dvd_pow h)
    · exact h3 (hp.dvd_of_dvd_pow h)
    · exact h4 h
  · rw [card_om8_eq, hs4, hq]
    ring

variable (H : Subgroup Kˣ)

@[expose] noncomputable def torusHom : (Fin 4 → H) →* Om8 K :=
  dgHom.comp (MonoidHom.pi fun k => H.subtype.comp (Pi.evalMonoidHom (fun _ => H) k))

theorem torusHom_apply (c : Fin 4 → H) : torusHom H c = dg (fun k => (c k : Kˣ)) := rfl

theorem dg_injective : Function.Injective (dg (K := K)) := by
  intro c c' h
  funext k
  have h1 : act (dg c) (Pi.single (ie k) 1) (ie k) = act (dg c') (Pi.single (ie k) 1) (ie k) := by
    rw [h]
  rw [act_dg_single, act_dg_single, twHom_ie, twHom_ie, Pi.smul_apply, Pi.smul_apply,
    Pi.single_eq_same, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at h1
  exact Units.ext h1

theorem torusHom_injective : Function.Injective (torusHom H) := by
  intro c c' h
  have h' : dg (fun k => (c k : Kˣ)) = dg (fun k => (c' k : Kˣ)) := h
  funext k
  exact Subtype.ext (congrFun (dg_injective h') k)

@[expose] noncomputable def torusSub : Subgroup (Om8 K) := (torusHom H).range

theorem card_torusSub : Nat.card (torusSub H) = Nat.card H ^ 4 := by
  rw [torusSub, ← Nat.card_congr (MonoidHom.ofInjective (torusHom_injective H)).toEquiv,
    Nat.card_fun, Nat.card_fin]

theorem wg_mem_normalizer_torusSub : wg ∈ Subgroup.normalizer ((torusSub H : Set (Om8 K))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun k => c (sig3 k), ?_⟩
    rw [torusHom_apply, torusHom_apply, wg_mul_dg, mul_inv_cancel_right]
  · rintro ⟨c, hc⟩
    refine ⟨fun k => c (sig3.symm k), ?_⟩
    rw [torusHom_apply] at hc ⊢
    have e1 : wg * dg (fun k => (c (sig3.symm k) : Kˣ)) = dg (fun k => (c k : Kˣ)) * wg := by
      rw [wg_mul_dg]
      congr 2
      funext k
      rw [Equiv.symm_apply_apply]
    have e2 : dg (fun k => (c (sig3.symm k) : Kˣ)) = wg⁻¹ * (dg (fun k => (c k : Kˣ)) * wg) := by
      rw [← e1, inv_mul_cancel_left]
    rw [e2, hc]
    group

theorem isPGroup_torusSub (hH : IsPGroup 3 H) : IsPGroup 3 (torusSub H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  exact IsPGroup.iff_card.mpr ⟨n * 4, by rw [card_torusSub, hn, ← pow_mul]⟩

@[expose] noncomputable def pThree : Subgroup (Om8 K) := torusSub H ⊔ Subgroup.zpowers wg

theorem isPGroup_pThree (hH : IsPGroup 3 H) : IsPGroup 3 (pThree H) :=
  (isPGroup_torusSub H hH).to_sup_of_normal_left' isPGroup_zpowers_wg
    (Subgroup.zpowers_le.mpr (wg_mem_normalizer_torusSub H))

theorem wg_not_mem_torusSub : wg ∉ torusSub H := by
  rintro ⟨c, hc⟩
  have h1 : act (torusHom H c) (Pi.single (ie 0) 1) (ie 2) =
      act wg (Pi.single (ie 0) (1 : K)) (ie 2) := by
    rw [hc]
  rw [torusHom_apply, act_dg_single, act_wg, Pi.smul_apply, Function.comp_apply, pi3_ie, sig3_two,
    Pi.single_eq_same, Pi.single_eq_of_ne (ie_injective.ne (by decide : (2 : Fin 4) ≠ 0)),
    smul_zero] at h1
  exact zero_ne_one h1

theorem card_torusSub_lt : Nat.card (torusSub H) < Nat.card (pThree H) :=
  Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => wg_not_mem_torusSub H (by
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers wg)))

omit [Finite K] [CharP K 2] in
theorem sig3_eq_three_iff (k : Fin 4) : sig3 k = 3 ↔ k = 3 := by
  fin_cases k <;> decide

theorem pThree_le_centralizer (ω : Kˣ) : pThree H ≤ Subgroup.centralizer {zStd ω} := by
  refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
  · rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, torusHom_apply, zStd, ← dgHom_apply,
      ← dgHom_apply, ← map_mul, ← map_mul]
    exact congrArg dgHom (mul_comm _ _)
  · rw [Subgroup.mem_centralizer_singleton_iff, zStd, wg_mul_dg]
    congr 2
    funext k
    simp only [sig3_eq_three_iff]

end L613C3

open L613C3

theorem ggD4ClassThreeStdSylowInput_holds : GGD4ClassThreeStdSylowInput := by
  intro K _ _ _ hK3 ω _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq2 : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨a, r, hr, hqr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := Nat.card K - 1) (by omega) 3
    (by norm_num)
  have ha : 1 ≤ a := by
    by_contra h
    have h0 : a = 0 := by omega
    rw [h0, pow_zero, one_mul] at hqr
    exact hr (hqr ▸ hK3)
  obtain ⟨m, hm, hcard⟩ := card_om8_eq_three_pow (K := K) hr hqr ha
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime (G := Kˣ) 3 (n := a)
    (by rw [Nat.card_units, hqr]; exact dvd_mul_right _ _)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (isPGroup_pThree H (IsPGroup.of_card hH))
  have hlt := card_torusSub_lt H
  rw [card_torusSub, hH, hk, ← pow_mul] at hlt
  have hk' : 4 * a + 1 ≤ k := by
    have := (pow_lt_pow_iff_right₀ (by norm_num : 1 < 3)).mp hlt
    omega
  have hdvdC : 3 ^ (4 * a + 1) ∣ Nat.card (Subgroup.centralizer {zStd ω}) :=
    (hk ▸ Nat.pow_dvd_pow 3 hk' : 3 ^ (4 * a + 1) ∣ Nat.card (pThree H)).trans
      (Subgroup.card_dvd_of_le (pThree_le_centralizer H ω))
  intro h3
  have hmul := Subgroup.index_mul_card (Subgroup.centralizer {zStd ω})
  rw [hcard] at hmul
  have hd : 3 * 3 ^ (4 * a + 1) ∣ 3 ^ (4 * a + 1) * m := hmul ▸ Nat.mul_dvd_mul h3 hdvdC
  rw [mul_comm 3] at hd
  exact hm ((Nat.mul_dvd_mul_iff_left (by positivity)).mp hd)

end CFSG.StandardType
