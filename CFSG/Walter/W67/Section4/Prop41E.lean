module

import CFSG.Walter.W67.Section4.Prop41A
import CFSG.Walter.W67.Section4.Prop41B
import CFSG.Walter.W67.Section4.Prop41C
import CFSG.Walter.W67.Section4.Prop41D
import CFSG.Walter.W67.Section4.Cor44
import CFSG.Walter.W67.Section4.Lemma42
import CFSG.Walter.W67.Section4.Lemma42A
import CFSG.Walter.W67.Section4.Lemma42B
import CFSG.Walter.W67.Section4.Prop43cA
import CFSG.Walter.W67.Section4.Basic
import CFSG.Walter.W67.W2Cor32A
public import CFSG.Walter.ReeOrder.JT.Section2
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

theorem not_dvd_24 {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) : ¬ ℓ ∣ 24 := by
  intro h
  have h' : ℓ ∣ 2 ^ 3 * 3 := h
  rcases (Nat.Prime.dvd_mul hℓ).mp h' with h1 | h1
  · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h1))
  · exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp h1)

theorem not_dvd_four {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) : ¬ ℓ ∣ 4 := by
  intro h
  have h' : ℓ ∣ 2 ^ 2 := h
  exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp (hℓ.dvd_of_dvd_pow h'))

variable {G : Type} [Group G] [Finite G]

namespace Std

variable (s : Std G) {T₂ : G}

theorem card_A
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2) :
    4 * Nat.card (s.fr.A T₂) = s.q + 1 := by
  obtain ⟨U₀, w, hU, -, hcard, hAU, hC⟩ := s.exists_torus hp hT₂ h2
  have hq8 := s.q_mod_eight hp
  have hcyc := hU.cyclic
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := U₀)
  have hgo : orderOf (g : G) = Nat.card U₀ := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  have h2U : 2 ∣ orderOf (g : G) := by rw [hgo]; omega
  set u := (g : G) ^ 2 with hu
  have huo : orderOf u = Nat.card U₀ / 2 := by
    rw [hu, orderOf_pow_of_dvd two_ne_zero h2U, hgo]
  have huU : u ∈ U₀ := U₀.pow_mem g.2 2
  have huodd : Odd (Nat.card (Subgroup.zpowers u)) := by
    rw [Nat.card_zpowers, huo]
    refine Nat.odd_iff.mpr ?_
    omega
  have hUC : U₀ ≤ s.K ⊓ Subgroup.centralizer ({T₂} : Set G) := by
    rw [hC]
    exact le_sup_left
  have hle : Subgroup.zpowers u ≤ s.fr.A T₂ := by
    refine le_oddPart (Subgroup.zpowers_le.mpr (hUC huU)) huodd ?_
    rw [hC]
    refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.mpr ?_)
    · refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
      have hab : ∀ a ∈ U₀, ∀ b ∈ U₀, a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val ((IsCyclic.isMulCommutative (α := U₀)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      have hxU : x ∈ U₀ := (Subgroup.zpowers_le.mpr huU) hx
      rw [hab y hy x hxU, mul_inv_cancel_right]
      exact hx
    · refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
      have hxU : x ∈ U₀ := (Subgroup.zpowers_le.mpr huU) hx
      rw [hU.inv x hxU]
      exact Subgroup.inv_mem _ hx
  have h1 : Nat.card U₀ / 2 ∣ Nat.card (s.fr.A T₂) := by
    rw [← huo, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hle
  have h2' : Nat.card (s.fr.A T₂) ∣ Nat.card U₀ / 2 := by
    have hAU' : Nat.card (s.fr.A T₂) ∣ Nat.card U₀ := Subgroup.card_dvd_of_le hAU
    have hU2 : Nat.card U₀ = 2 * (Nat.card U₀ / 2) := by omega
    rw [hU2] at hAU'
    exact (Nat.coprime_two_right.mpr (s.fr.odd_card_A T₂)).dvd_of_dvd_mul_left hAU'
  have := Nat.dvd_antisymm h1 h2'
  omega

theorem factorization_card_A_eq
    (hp : s.p = 3) (hT₂ : T₂ ∈ s.fr.T) (h2 : orderOf T₂ = 2)
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hℓq : ℓ ∣ s.q + 1) :
    (Nat.card (s.fr.A T₂)).factorization ℓ = (Nat.card s.K).factorization ℓ := by
  have hℓ : ℓ.Prime := Fact.out
  have h4A := s.card_A hp hT₂ h2
  have hq8 := s.q_mod_eight hp
  have hq5 := s.five_lt_q hp
  have hq1 : 1 ≤ s.q := by omega
  have hq2 : 1 ≤ s.q ^ 2 := Nat.one_le_pow _ _ hq1
  have hsq : s.q ^ 2 - 1 = (s.q - 1) * (s.q + 1) := by
    zify [hq1, hq2]
    ring
  have hK2 : 2 * Nat.card s.K = s.q * ((s.q - 1) * (s.q + 1)) := by
    rw [s.card_K, ← hsq]
    refine Nat.mul_div_cancel' ?_
    have hodd : Odd s.q := s.odd_p.pow
    have : Even (s.q ^ 2 - 1) := by
      rw [Nat.even_sub hq2]
      simp [Nat.even_pow, Nat.not_even_iff_odd.mpr hodd]
    exact (even_iff_two_dvd.mp this).mul_left _
  have hℓq' : ¬ ℓ ∣ s.q := by
    intro h
    rw [Hyp.q, hp] at h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp (hℓ.dvd_of_dvd_pow h))
  have hℓq1 : ¬ ℓ ∣ s.q - 1 := by
    intro h
    have h' := Nat.dvd_sub hℓq h
    rw [show s.q + 1 - (s.q - 1) = 2 by omega] at h'
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h')
  have e1 := congrArg (fun n => n.factorization ℓ) hK2
  have e2 := congrArg (fun n => n.factorization ℓ) h4A
  rw [Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ
      Nat.prime_two).mp h)), zero_add,
    Nat.factorization_mul (by omega) (Nat.mul_ne_zero (by omega) (by omega)), Finsupp.add_apply,
    Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hℓq', Nat.factorization_eq_zero_of_not_dvd hℓq1,
    zero_add, zero_add] at e1
  rw [Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (not_dvd_four hℓ hℓ2), zero_add] at e2
  rw [e1, e2]

theorem false_of_even_torus
    (hp : s.p = 3) {ℓ : ℕ} [Fact ℓ.Prime] (hℓσ : ℓ ∈ s.fr.σ)
    (hℓ3 : ℓ ≠ 3) (hℓq : ℓ ∣ s.q + 1) : False := by
  have hℓ : ℓ.Prime := Fact.out
  have hℓE : ℓ ∣ Nat.card s.fr.E := (Nat.mem_primeFactors.mp hℓσ).2.1
  have hℓ2 : ℓ ≠ 2 := fun h => by
    subst h
    exact (Nat.not_even_iff_odd.mpr s.fr.odd_card_E) (even_iff_two_dvd.mpr hℓE)
  have hℓp : ℓ ≠ s.p := by rw [hp]; exact hℓ3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT4 : Nat.card s.fr.T = 4 := s.fr.card_T
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := s.fr.T) 2 (by rw [hT4]; norm_num)
  have hT₂ : (t : G) ∈ s.fr.T := t.2
  have h2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have hA := s.isCyclic_A hp hT₂ h2
  have hAK : s.fr.A (t : G) ≤ s.K := fun x hx => (s.fr.A_le (t : G) hx).1
  obtain ⟨P₀, hP₀E, hP₀ℓ, hP₀ne, hP₀card⟩ := s.exists_sylow_E hℓE
  obtain ⟨Aℓ, -, hAℓA, -, hAℓcard⟩ :=
    exists_sylow_le_of_le (bot_le : ⊥ ≤ s.fr.A (t : G)) (IsPGroup.of_bot (p := ℓ))
  rw [s.factorization_card_A_eq hp hT₂ h2 hℓ2 hℓ3 hℓq] at hAℓcard
  have hP₀N : P₀ ≤ Subgroup.normalizer (Aℓ : Set G) := fun e he =>
    mem_normalizer_of_le_cyclic hA hAℓA (s.E_le_normalizer_A hT₂ (hP₀E he))
  have hc := card_sup_mul_card_inf_of_le_normalizer hP₀N
  have hinf : Aℓ ⊓ P₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have : x ∈ s.fr.A (t : G) ⊓ s.fr.E := ⟨hAℓA hx1, hP₀E hx2⟩
    rwa [s.A_inf_E] at this
  rw [hinf, Subgroup.card_bot, mul_one, hAℓcard, hP₀card, ← pow_add,
    ← s.factorization_card_H hℓ hℓ2] at hc
  have hPℓ : IsPGroup ℓ (Aℓ ⊔ P₀ : Subgroup G) := IsPGroup.of_card hc
  have hPH : Aℓ ⊔ P₀ ≤ s.H :=
    sup_le ((hAℓA.trans hAK).trans s.K_le_H) (hP₀E.trans s.fr.E_le_H)
  have hP₀P : P₀ ≤ Aℓ ⊔ P₀ := le_sup_right
  have hℓA : ℓ ∣ Nat.card (s.fr.A (t : G)) := by
    have h4A := s.card_A hp hT₂ h2
    rw [← h4A] at hℓq
    rcases (Nat.Prime.dvd_mul hℓ).mp hℓq with h | h
    · exact absurd h (not_dvd_four hℓ hℓ2)
    · exact h
  have hℓK : ℓ ∣ Nat.card s.K := hℓA.trans (Subgroup.card_dvd_of_le hAK)
  have hnc := s.not_isMulCommutative hℓ2 hℓp hℓK hP₀E hP₀ℓ hP₀ne hPH hPℓ hc hP₀P
  have hmc := s.isMetacyclic hℓ2 hℓp hP₀E hP₀card hPH hPℓ hc hP₀P
  have hPK : (Aℓ ⊔ P₀) ⊓ s.K = Aℓ := by
    refine (Subgroup.eq_of_le_of_card_ge (le_inf le_sup_left (hAℓA.trans hAK)) ?_).symm
    rw [s.card_inf_K hℓ2 hPH hPℓ hc, hAℓcard]
  have hcomm : ⁅Aℓ ⊔ P₀, Aℓ ⊔ P₀⁆ ≤ Aℓ := by
    have h : ⁅Aℓ ⊔ P₀, Aℓ ⊔ P₀⁆ ≤ (Aℓ ⊔ P₀) ⊓ s.K := by
      refine le_inf (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
        ((Subgroup.commutator_mono hPH hPH).trans s.commutator_H_le_K)
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
        (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
    rwa [hPK] at h
  have hcne : ⁅Aℓ ⊔ P₀, Aℓ ⊔ P₀⁆ ≠ ⊥ := by
    intro h
    apply hnc
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact ⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp (h a.2) b b.2).symm⟩⟩
  have hNV : Subgroup.normalizer ((Aℓ ⊔ P₀ : Subgroup G) : Set G) ≤
      Subgroup.normalizer (s.fr.V (t : G) : Set G) := by
    rw [← s.normalizer_eq_of lemma_4_2 hp hT₂ h2 (hcomm.trans hAℓA) hcne]
    intro g hg
    exact mem_normalizer_commutator' hg hg
  have hfac : (Nat.card (Subgroup.normalizer ((Aℓ ⊔ P₀ : Subgroup G) : Set G))).factorization ℓ ≤
      (Nat.card (Aℓ ⊔ P₀ : Subgroup G)).factorization ℓ := by
    have h1 := (Subgroup.card_dvd_of_le hNV).trans (s.card_normalizer_V_dvd hp hT₂ h2)
    have h3 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (Nat.mul_ne_zero (by norm_num)
      (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'))).mpr h1 ℓ
    rw [Nat.factorization_mul (by norm_num) (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'),
      Finsupp.add_apply, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (not_dvd_24 hℓ hℓ2 hℓ3),
      zero_add, s.factorization_card_A_eq hp hT₂ h2 hℓ2 hℓ3 hℓq] at h3
    rw [hc, Nat.factorization_pow_self hℓ, s.factorization_card_H hℓ hℓ2]
    exact h3
  obtain ⟨RG, hPRG⟩ := hPℓ.exists_le_sylow
  have hPRG' := eq_of_le_of_factorization_le RG.isPGroup' hPRG hfac
  refine false_of_perfect_of_metacyclic s.perfect hℓ2 RG ?_ ?_
  · rw [← hPRG']
    exact hnc
  · rw [← hPRG']
    exact hmc

theorem f_eq_of_p_five
    (hR : RFacts) (hp5 : s.p = 5) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓσ : ℓ ∈ s.fr.σ) : s.f = ℓ := by
  have hℓ : ℓ.Prime := Fact.out
  have hℓE : ℓ ∣ Nat.card s.fr.E := (Nat.mem_primeFactors.mp hℓσ).2.1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := s.fr.E) ℓ hℓE
  have hΩE : Subgroup.zpowers (x : G) ≤ s.fr.E := Subgroup.zpowers_le.mpr x.2
  have hΩcard : Nat.card (Subgroup.zpowers (x : G)) = ℓ := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]
  have hΩne : Subgroup.zpowers (x : G) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hΩcard
    exact hℓ.one_lt.ne hΩcard
  obtain ⟨hedvd, -, -⟩ := lemma_2_6_i G s.toHyp s.fr hΩE hΩne
  have heΩ : s.eX (Subgroup.zpowers (x : G)) = ℓ := by rw [s.eX_eq, hΩcard]
  have hLS := s.L_spec _ hΩE hΩne
  obtain ⟨K', hJR, -⟩ := hLS.jr
  have hfe0 : 0 < s.f / s.eX (Subgroup.zpowers (x : G)) := by
    rw [heΩ]
    exact Nat.div_pos (Nat.le_of_dvd s.f_pos (heΩ ▸ hedvd)) hℓ.pos
  obtain ⟨hL', hLp, hLf, -, -⟩ := IsJRSubgroup.nonempty_jrGroup G s.p_ne_two hfe0 hJR
  have hqL : hL'.q = s.p ^ (s.f / s.eX (Subgroup.zpowers (x : G))) := by
    rw [JRGroup.q, hLp, hLf]
  rw [heΩ, hp5] at hqL
  rw [heΩ] at hedvd hfe0
  by_cases h5' : hL'.q = 5
  · rw [h5'] at hqL
    have h1 : s.f / ℓ = 1 :=
      Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 5))
        (show 5 ^ (s.f / ℓ) = 5 ^ 1 by rw [pow_one]; exact hqL.symm)
    have := Nat.div_mul_cancel hedvd
    rw [h1, one_mul] at this
    exact this.symm
  · exfalso
    obtain ⟨⟨⟨m, -, hqm⟩, -, -, -⟩, -, -, -, -, -, -⟩ := hR _ hL' h5'
    rw [hqm] at hqL
    have h1 : 5 ∣ 3 ^ m := by
      rw [hqL]
      exact dvd_pow_self 5 hfe0.ne'
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_five Nat.prime_three).mp
      (Nat.prime_five.dvd_of_dvd_pow h1)
    norm_num at this

end Std

end CFSG.Walter.W67
