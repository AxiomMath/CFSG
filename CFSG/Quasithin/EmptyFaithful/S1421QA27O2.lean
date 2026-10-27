module

public import CFSG.Quasithin.EmptyFaithful.S1421QA18Order
public import CFSG.Quasithin.EmptyFaithful.S1421QA27Surv
public import CFSG.Quasithin.EmptyFaithful.S1421Hyp111
public import CFSG.Quasithin.EmptyFaithful.S1421QA17AutData

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421QA27

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem isPGroup_sOf (st : Setting1427 T M H K1) : IsPGroup 2 (S1421.sOf T K1) :=
  st.hyp.sylow.1.to_le S1421.sOf_le_T

omit [Finite G] in
theorem sOf_le_normalizer : S1421.sOf T K1 ≤ Subgroup.normalizer (K1 : Set G) := inf_le_right

omit [Finite G] in
theorem sup_sOf_le_normalizer : K1 ⊔ S1421.sOf T K1 ≤ Subgroup.normalizer (K1 : Set G) :=
  sup_le Subgroup.le_normalizer sOf_le_normalizer

omit [Finite G] in
theorem sup_sOf_le_normalizer_pCoreOf :
    K1 ⊔ S1421.sOf T K1 ≤ Subgroup.normalizer (pCoreOf 2 K1 : Set G) :=
  F7.le_normalizer_pCoreOf_of_le_normalizer sup_sOf_le_normalizer

theorem pCoreOf_le_pCoreOf_sup : pCoreOf 2 K1 ≤ pCoreOf 2 (K1 ⊔ S1421.sOf T K1) :=
  le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K1).trans le_sup_left) sup_sOf_le_normalizer_pCoreOf
    (pCoreOf_isPGroup 2 K1)

theorem pCoreOf_sup_le_of_card_le (h : Nat.card ↥(K1 ⊔ S1421.sOf T K1) ≤ Nat.card ↥K1) :
    pCoreOf 2 (K1 ⊔ S1421.sOf T K1) ≤ pCoreOf 2 K1 := by
  have : K1 = K1 ⊔ S1421.sOf T K1 := Subgroup.eq_of_le_of_card_ge le_sup_left h
  rw [← this]

omit [Finite G] in
theorem card_sup_dvd {L2 : Subgroup G} {Y : Type} [Group Y]
    (ψ : ↥(K1 ⊔ bigB K1 L2 (S1421.sOf T K1)) →* Y) (hψ : Function.Injective ψ) :
    Nat.card ↥(K1 ⊔ S1421.sOf T K1) ∣ Nat.card Y := by
  have hX : K1 ⊔ S1421.sOf T K1 ≤ K1 ⊔ bigB K1 L2 (S1421.sOf T K1) := sup_le_sup_bigB
  exact Subgroup.card_dvd_of_injective (ψ.comp (Subgroup.inclusion hX))
    (hψ.comp (Subgroup.inclusion_injective _))

theorem eq_zero_of_two_pow_dvd {j m : ℕ} (hm : m % 2 = 1) (h : 2 ^ j ∣ m) : j = 0 := by
  by_contra hj
  have h2 : 2 ∣ m := (dvd_pow_self 2 hj).trans h
  omega

theorem card_of_equiv_mulAut_quasithinJ2
    {Y : Type} [Group Y]
    (h : Nonempty (Y ≃* MulAut quasithinJ2)) : Nat.card Y = 1209600 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr (e.trans S1421QA17.mulAutQuasithinJ2EquivNative).toEquiv,
    CFSG.ComponentClassification.J2Cover.j2_mulAut_card, CFSG.Sporadic.J2.card_J2]

theorem qo2_survivor4
    (st : Setting1427 T M H K1)
    (hsurv : Survivor4LegacyBare K1 (S1421.l2Of T H (yOfL22 T M)) (S1421.sOf T K1)) :
    pCoreOf 2 (K1 ⊔ S1421.sOf T K1) ≤ pCoreOf 2 K1 := by
  obtain ⟨hA, hq1, hsp, -, -⟩ := hsurv
  obtain ⟨Y, _, ψ, hY, hψ⟩ := exists_emb_of_isAmalgamOfGroup hA
  have hdvd := card_sup_dvd ψ hψ
  obtain ⟨j, hj⟩ := exists_card_sup_eq (isPGroup_sOf st) sOf_le_normalizer
  rw [d4Order_holds Y hY, hj, card_K1_of_survivor4 hq1 hsp] at hdvd
  have h819 : 2 ^ j ∣ 819 := by
    have h : 258048 * 2 ^ j ∣ 258048 * 819 := by
      rw [show (258048 : ℕ) * 819 = 211341312 by norm_num]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hj0 := eq_zero_of_two_pow_dvd (by norm_num) h819
  exact pCoreOf_sup_le_of_card_le (by rw [hj, hj0, pow_zero, mul_one])

end S1421QA27

end CFSG.Quasithin
