module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SmallK
import CFSG.Quasithin.Vol2.Ch12Sec6P31b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A H T : Subgroup (MulAut W)}

theorem ThreeNat.parabolic_of_isAlt_five
    (h : ThreeNat A H T) (hA5 : UC22.IsAlt ↥H 5) :
    T3Parab H T 1 := by
  obtain ⟨e⟩ := hA5
  let P : Subgroup (MulAut W) := T ⊓ H
  let Q : Subgroup (MulAut W) := H ⊓ Subgroup.normalizer (P : Set (MulAut W))
  have hSylH : CFSG.ABGLocalTools.IsSylowOf 2 P H :=
    h.sylow.inf_of_le_normalizer h.le h.normal
  have hSylTwo : CFSG.QuasithinUnique.IsSylowTwoOf P H := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff] at hSylH
    exact hSylH
  have hcardP : Nat.card ↥P = 4 :=
    CFSG.Quasithin.H13.S126P31.card_sylow_of_alt5 e hSylTwo
  have hcardQ : Nat.card ↥Q = 12 :=
    CFSG.Quasithin.H13.S126P31.card_inf_normalizer e hSylTwo
  have hTnormP : T ≤ Subgroup.normalizer (P : Set (MulAut W)) :=
    (le_inf Subgroup.le_normalizer (h.sylow.le.trans h.normal)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTnormQ : T ≤ Subgroup.normalizer (Q : Set (MulAut W)) :=
    (le_inf (h.sylow.le.trans h.normal) (hTnormP.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hTQ : ∀ t ∈ T, ∀ x ∈ Q, t * x * t⁻¹ ∈ Q :=
    fun t ht x hx => (Subgroup.mem_set_normalizer_iff.mp (hTnormQ ht) x).mp hx
  have hPQ : P ≤ Q := le_inf inf_le_right Subgroup.le_normalizer
  have hcard : Nat.card ↥Q = 3 ^ 1 * Nat.card ↥P := by
    rw [hcardQ, hcardP]
    norm_num
  have hexp : ∀ x ∈ Q, ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1 := by
    intro x hx n hxn
    have hdvd12 : orderOf x ∣ 12 := by
      have h := orderOf_dvd_natCard (⟨x, hx⟩ : ↥Q)
      rw [← Subgroup.orderOf_coe] at h
      rwa [hcardQ] at h
    have hdvd3n : orderOf x ∣ 3 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hxn
    obtain ⟨k, hk, hpow⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd3n
    rw [hpow] at hdvd12
    have hk1 : k ≤ 1 := by
      by_contra hk1
      have h2 : 2 ≤ k := by omega
      have h9 : 9 ∣ 3 ^ k := pow_dvd_pow 3 h2
      have h912 : 9 ∣ 12 := h9.trans hdvd12
      norm_num at h912
    have h3 : 3 ^ k ∣ 3 := pow_dvd_pow 3 hk1
    have hdvd3 : orderOf x ∣ 3 := by
      rwa [hpow]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd3
  exact T3Parab.of_normalized h (show Q ≤ H from inf_le_left) hTQ hPQ hcard hexp

theorem ThreeNat.parabolicK_of_isAlt_five
    (h : ThreeNat A H T) (hA5 : UC22.IsAlt ↥H 5)
    (h7 : Nat.card ↥(irrSet H) = 7)
    (hK : Nat.card ↥(s1t3KBar A H) = 168) :
    T3ParabK H (s1t3KBar A H) T 2 := by
  have h1 : T3Parab H T 1 := h.parabolic_of_isAlt_five hA5
  simpa using T3ParabK.of_kBar h h7 hK h1
