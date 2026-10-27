module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNonsAsm
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNonsTor
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNonsOrders
public import CFSG.LocalAnalysis.StandardType.GGKGForkWeylSeven
import CFSG.LocalAnalysis.StandardType.GGKGForkExcNonsLang

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

private theorem ggKGE8n_not_dvd_weylCard {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) :
    ¬ p ∣ 696729600 := by
  intro h
  have hfac : (696729600 : ℕ) = 2 ^ 14 * 3 ^ 5 * 5 ^ 2 * 7 := by norm_num
  rw [hfac] at h
  rcases hp.dvd_mul.mp h with h | h7
  · rcases hp.dvd_mul.mp h with h | h5
    · rcases hp.dvd_mul.mp h with h | h3
      · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
        have := Nat.le_of_dvd (by norm_num) h2
        omega
      · have h3' : p ∣ 3 := hp.dvd_of_dvd_pow h3
        have := Nat.le_of_dvd (by norm_num) h3'
        omega
    · have h5' : p ∣ 5 := hp.dvd_of_dvd_pow h5
      have := Nat.le_of_dvd (by norm_num) h5'
      omega
  · have h7' : p ∣ 7 := h7
    have := Nat.le_of_dvd (by norm_num) h7'
    omega

private theorem ggKGE8n_padicValNat_seven_weyl :
    padicValNat 7 696729600 = 1 := by
  rw [show (696729600 : ℕ) = 7 * (2 ^ 14 * 3 ^ 5 * 5 ^ 2) by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

private theorem ggKGE8n_p7
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (E : Subgroup (adjointGroup .E8 K)) (hE : IsElemAbelian 7 E)
    (hcard : 7 ^ 7 ≤ Nat.card E)
    (hsc : ∀ g : adjointGroup .E8 K, (∀ e ∈ E, g * e = e * g) → g ^ 7 = 1 → g ∈ E)
    (hpq : 7 ∣ Nat.card K + 1) :
    ∃ F : ExcFrame .E8 K 7 E, (7 ∣ Nat.card K - 1 → F.w = 1) ∧
      (7 ∣ Nat.card K + 1 → ExcIsLongest .E8 F.w) := by
  have h3 : 7 ^ 3 ≤ Nat.card E :=
    le_trans (Nat.pow_le_pow_right (by norm_num : 0 < 7) (by norm_num : 3 ≤ 7)) hcard
  refine ExcNons.excSCTorusInput_nons_of_toral (τ := .E8) (r₀ := 7)
    (by norm_num : 5 ≤ 7) hpq ?_ E hE h3 hcard hsc
  intro E' hE' hr' hsc'
  refine ExcNons.exists_nons_frame_conj_into_torus (τ := .E8) (Or.inr rfl)
    (by norm_num : Nat.Prime 7) (by norm_num : 5 ≤ 7) hpq ?_ (m := 3) ?_ E' hE' ?_
  · rw [Nat.factorization_def _ (by norm_num : Nat.Prime 7),
      ExcNons.padicValNat_card_adjointGroup_E8_nons (by norm_num : Nat.Prime 7)
        (by norm_num : 5 ≤ 7) hpq, ggKGE8n_padicValNat_seven_weyl]
    show 8 * padicValNat 7 (Nat.card K + 1) + 1 ≤
      8 * padicValNat 7 (Nat.card K + 1) + 1
    omega
  · intro C _ hC w hw
    exact weylE8_seven_fixed hC hw
  · exact le_trans (Nat.pow_le_pow_right (by norm_num : 0 < 7) (by norm_num : 5 ≤ 7)) hr'

private theorem ggKGE8n_pge11
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (E : Subgroup (adjointGroup .E8 K)) (hE : IsElemAbelian p E)
    (hcard : p ^ 7 ≤ Nat.card E)
    (hsc : ∀ g : adjointGroup .E8 K, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E)
    (hpq : p ∣ Nat.card K + 1) :
    ∃ F : ExcFrame .E8 K p E, (p ∣ Nat.card K - 1 → F.w = 1) ∧
      (p ∣ Nat.card K + 1 → ExcIsLongest .E8 F.w) := by
  have h3 : p ^ 3 ≤ Nat.card E :=
    le_trans (Nat.pow_le_pow_right (by omega : 0 < p) (by norm_num : 3 ≤ 7)) hcard
  refine ExcNons.excSCTorusInput_nons_of_toral (τ := .E8) (r₀ := 7)
    (by omega) hpq ?_ E hE h3 hcard hsc
  intro E' hE' hr' hsc'
  refine ExcNons.exists_nons_frame_conj_into_torus (τ := .E8) (Or.inr rfl) hp (by omega) hpq
    ?_ (m := 0) ?_ E' hE' ?_
  · rw [Nat.factorization_def _ hp,
      ExcNons.padicValNat_card_adjointGroup_E8_nons hp (by omega) hpq,
      padicValNat.eq_zero_of_not_dvd (ggKGE8n_not_dvd_weylCard hp hp11)]
    show 8 * padicValNat p (Nat.card K + 1) + 0 ≤
      8 * padicValNat p (Nat.card K + 1) + 1
    omega
  · intro C _ hC w hw
    exfalso
    have hdvd : p ∣ Nat.card (WeylGroup .E8) := hw ▸ orderOf_dvd_natCard w
    rw [card_weylGroup_E8'] at hdvd
    exact ggKGE8n_not_dvd_weylCard hp hp11 hdvd
  · exact le_trans (Nat.pow_le_pow_right (by omega : 0 < p) (by norm_num : 2 ≤ 7)) hr'

theorem excSCTorusInput_E8_nonsplit
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    ExcSCTorusInput .E8 K p 7 := by
  intro E hE h3 hr hsc
  by_cases h5 : p = 5
  · subst h5
    exact excSCTorusInput_nonsplit_three_five (τ := .E8) (Or.inr rfl) (Or.inr rfl) hpq
      E hE h3 hr hsc
  · have hp7 : 7 ≤ p := by
      have hp_ne6 : p ≠ 6 := by rintro rfl; norm_num at hp
      omega
    by_cases h7 : p = 7
    · subst h7
      exact ggKGE8n_p7 E hE (by simpa using hr) (by simpa using hsc) hpq
    · have hp11 : 11 ≤ p := by
        have hp_ne8 : p ≠ 8 := by rintro rfl; norm_num at hp
        have hp_ne9 : p ≠ 9 := by rintro rfl; norm_num at hp
        have hp_ne10 : p ≠ 10 := by rintro rfl; norm_num at hp
        omega
      exact ggKGE8n_pge11 hp hp11 E hE hr hsc hpq

theorem ggKGExcInputNonsplit_E8
    :
    GGKGExcInputNonsplit .E8 7 :=
  fun _ _ _ _ _ hp hp5 hpq => excSCTorusInput_E8_nonsplit hp hp5 hpq

end CFSG.StandardType

end
