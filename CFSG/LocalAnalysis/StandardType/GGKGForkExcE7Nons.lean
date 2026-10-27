module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNonsAsm
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNonsTor
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNonsOrders
public import CFSG.LocalAnalysis.StandardType.GGKGForkWeylSeven
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley

private theorem ggKGE7n_padicValNat_2903040_le_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    padicValNat p 2903040 ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : padicValNat p (2 ^ 10) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have h2d : p ∣ 2 := hp.dvd_of_dvd_pow h
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2d
    omega
  have h3 : padicValNat p (3 ^ 4) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have h3d : p ∣ 3 := hp.dvd_of_dvd_pow h
    have : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3d
    omega
  have hsum : padicValNat p 5 + padicValNat p 7 ≤ 1 := by
    by_cases h5 : p = 5
    · subst p
      rw [padicValNat_base (by norm_num : 1 < 5),
        padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 5 ∣ 7)] <;> omega
    · by_cases h7 : p = 7
      · subst p
        rw [padicValNat_base (by norm_num : 1 < 7),
          padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 5)] <;> omega
      · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
        rw [padicValNat_primes (p := p) (q := 5) h5,
          padicValNat_primes (p := p) (q := 7) h7] <;> omega
  calc padicValNat p 2903040
      = padicValNat p (2 ^ 10 * 3 ^ 4) + padicValNat p (5 * 7) := by
        rw [show (2903040 : ℕ) = (2 ^ 10 * 3 ^ 4) * (5 * 7) by norm_num,
          padicValNat.mul (by norm_num) (by norm_num)]
    _ = (padicValNat p (2 ^ 10) + padicValNat p (3 ^ 4)) +
          (padicValNat p 5 + padicValNat p 7) := by
        rw [padicValNat.mul (by norm_num) (by norm_num),
          padicValNat.mul (by norm_num) (by norm_num)]
    _ ≤ 1 := by rw [h2, h3]; omega

private theorem ggKGE7n_not_dvd_2903040 {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ p ∣ 2903040 := by
  intro h
  have hfac : p ∣ 2 ^ 10 * (3 ^ 4 * (5 * 7)) := by
    rwa [show (2903040 : ℕ) = 2 ^ 10 * (3 ^ 4 * (5 * 7)) by norm_num] at h
  rcases hp.dvd_mul.mp hfac with h | h
  · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
    have : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  rcases hp.dvd_mul.mp h with h | h
  · have h3 : p ∣ 3 := hp.dvd_of_dvd_pow h
    have : p ≤ 3 := Nat.le_of_dvd (by norm_num) h3
    omega
  rcases hp.dvd_mul.mp h with h | h
  · have : p ≤ 5 := Nat.le_of_dvd (by norm_num) h
    omega
  · have : p ≤ 7 := Nat.le_of_dvd (by norm_num) h
    omega

private theorem ggKGE7n_prime_cases {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    p = 5 ∨ p = 7 ∨ 11 ≤ p := by
  by_cases h : p < 11
  · interval_cases p
    · exact Or.inl rfl
    · exact absurd hp (by norm_num)
    · exact Or.inr (Or.inl rfl)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
  · omega

private theorem ggKGE7n_toral_of_weyl
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) {m : ℕ} (hm : m ≤ 4)
    (hord : (Nat.card (adjointGroup .E7 K)).factorization p ≤
      7 * padicValNat p (Nat.card K + 1) + 1)
    (hW : ∀ {C : Type} [CommGroup C], Nat.card C = p →
      ∀ {w : CFSG.LieType.Chevalley.WeylGroup .E7}, orderOf w = p →
      Nat.card {a : Fin Tag.E7.rank → C //
        CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.mactC
          (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.Atw w) a = a} ≤ p ^ m) :
    ExcSCTorusInput .E7 K p 6 := by
  refine ExcNons.excSCTorusInput_nons_of_toral (τ := .E7) hp5 hpq ?_
  intro E hE hr6 hsc
  refine ExcNons.exists_nons_frame_conj_into_torus (τ := .E7) (Or.inl rfl) hp hp5 hpq hord hW
    E hE ?_
  calc p ^ (m + 2) ≤ p ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ Nat.card E := hr6

theorem excSCTorusInput_E7_nonsplit
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    ExcSCTorusInput .E7 K p 6 := by
  rcases ggKGE7n_prime_cases hp hp5 with h5 | h7 | h11
  · subst p
    have hord : (Nat.card (adjointGroup .E7 K)).factorization 5 ≤
        7 * padicValNat 5 (Nat.card K + 1) + 1 := by
      rw [Nat.factorization_def _ hp,
        ExcNons.padicValNat_card_adjointGroup_E7_nons (K := K) hp hp5 hpq]
      have hb := ggKGE7n_padicValNat_2903040_le_one hp hp5
      omega
    have hW : ∀ {C : Type} [CommGroup C], Nat.card C = 5 →
        ∀ {w : CFSG.LieType.Chevalley.WeylGroup .E7}, orderOf w = 5 →
        Nat.card {a : Fin Tag.E7.rank → C //
          CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.mactC
            (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.Atw w) a = a} ≤ 5 ^ 4 := by
      intro C _ hC w hw
      exact weylE7_five_fixed (C := C) hC hw
    exact ggKGE7n_toral_of_weyl hp hp5 hpq (m := 4) (by norm_num) hord hW
  · subst p
    have hord : (Nat.card (adjointGroup .E7 K)).factorization 7 ≤
        7 * padicValNat 7 (Nat.card K + 1) + 1 := by
      rw [Nat.factorization_def _ hp,
        ExcNons.padicValNat_card_adjointGroup_E7_nons (K := K) hp hp5 hpq]
      have hb := ggKGE7n_padicValNat_2903040_le_one hp hp5
      omega
    have hW : ∀ {C : Type} [CommGroup C], Nat.card C = 7 →
        ∀ {w : CFSG.LieType.Chevalley.WeylGroup .E7}, orderOf w = 7 →
        Nat.card {a : Fin Tag.E7.rank → C //
          CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.mactC
            (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.Atw w) a = a} ≤ 7 ^ 2 := by
      intro C _ hC w hw
      exact weylE7_seven_fixed (C := C) hC hw
    exact ggKGE7n_toral_of_weyl hp hp5 hpq (m := 2) (by norm_num) hord hW
  · have hord : (Nat.card (adjointGroup .E7 K)).factorization p ≤
        7 * padicValNat p (Nat.card K + 1) + 1 := by
      rw [Nat.factorization_def _ hp,
        ExcNons.padicValNat_card_adjointGroup_E7_nons (K := K) hp hp5 hpq]
      have hb := ggKGE7n_padicValNat_2903040_le_one hp hp5
      omega
    have hW : ∀ {C : Type} [CommGroup C], Nat.card C = p →
        ∀ {w : CFSG.LieType.Chevalley.WeylGroup .E7}, orderOf w = p →
        Nat.card {a : Fin Tag.E7.rank → C //
          CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.mactC
            (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.Atw w) a = a} ≤ p ^ 0 := by
      intro C _ hC w hw
      exfalso
      have hdvd : p ∣ Nat.card (CFSG.LieType.Chevalley.WeylGroup .E7) := by
        rw [← hw]
        exact orderOf_dvd_natCard w
      rw [CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E7'] at hdvd
      exact ggKGE7n_not_dvd_2903040 hp h11 hdvd
    exact ggKGE7n_toral_of_weyl hp hp5 hpq (m := 0) (by norm_num) hord hW

theorem ggKGExcInputNonsplit_E7
    :
    GGKGExcInputNonsplit .E7 6 :=
  fun _ _ _ _ _ hp hp5 hpq => excSCTorusInput_E7_nonsplit hp hp5 hpq

end CFSG.StandardType

end
