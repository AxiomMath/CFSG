module

public import CFSG.Walter.W67.Statements
public import CFSG.Walter.W67.Section4.Cor44A
import CFSG.Walter.W67.Section4.Prop41A
import CFSG.Walter.W67.Section4.Prop41B
import CFSG.Walter.W67.Section4.Prop41C
import CFSG.Walter.W67.Section4.Prop41D
import CFSG.Walter.W67.Section4.Prop41E
import CFSG.Walter.W67.Section4.Cor44
import CFSG.Walter.W67.Section4.Lemma42B
import CFSG.Walter.W67.Lemma21

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

theorem prop_4_1_three :
    S_prop_4_1_three := by
  intro G _ _ s hR hp r hr
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hr3, hrq⟩ := hcon
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have : Fact r.Prime := ⟨hrp⟩
  have hr2 : r ≠ 2 := fun h => by
    subst h
    exact (Nat.not_even_iff_odd.mpr s.fr.odd_card_E)
      (even_iff_two_dvd.mpr (Nat.mem_primeFactors.mp hr).2.1)
  have hJ : s.p ≠ 3 → JFacts := fun h => absurd hp h
  have h3 : s.p = 3 → r ≠ 3 ∧ ¬ r ∣ s.q ^ 2 - s.q + 1 := fun _ => ⟨hr3, hrq⟩
  have h5 : s.p = 5 → r ≠ 7 ∧ r ≠ 11 ∧ r ≠ 19 := fun h => absurd (hp.symm.trans h) (by norm_num)
  have hrK := s.dvd_card_K hJ hR hr h3 h5
  have hrp' : r ≠ s.p := by rw [hp]; exact hr3
  have hq8 := s.q_mod_eight hp
  have hq1 : 1 ≤ s.q := by omega
  have hq2 : 1 ≤ s.q ^ 2 := Nat.one_le_pow _ _ hq1
  have hdvd : r ∣ s.q * ((s.q - 1) * (s.q + 1)) := by
    have hsq : s.q ^ 2 - 1 = (s.q - 1) * (s.q + 1) := by
      zify [hq1, hq2]
      ring
    rw [← hsq]
    exact hrK.trans (s.card_K ▸ Nat.div_dvd_of_dvd (by
      have hodd : Odd s.q := s.odd_p.pow
      have : Even (s.q ^ 2 - 1) := by
        rw [Nat.even_sub hq2]
        simp [Nat.even_pow, Nat.not_even_iff_odd.mpr hodd]
      exact (even_iff_two_dvd.mp this).mul_left _))
  rcases (Nat.Prime.dvd_mul hrp).mp hdvd with h | h
  · rw [Hyp.q, hp] at h
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_three).mp (hrp.dvd_of_dvd_pow h))
  rcases (Nat.Prime.dvd_mul hrp).mp h with h | h
  · refine s.false_of_odd_torus hJ hR hr hrp' h3 h5 ⟨fun _ h' => ?_, fun h4 => by omega⟩
    have h'' := Nat.dvd_sub h' h
    rw [show s.q + 1 - (s.q - 1) = 2 by omega] at h''
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp h'')
  · exact s.false_of_even_torus hp hr hr3 h

theorem cor_4_4 :
    S_cor_4_4 := cor_4_4_of prop_4_1_three

theorem prop_4_1 :
    S_prop_4_1 := by
  intro G _ _ s hJF hR r hr
  refine ⟨fun hp => prop_4_1_three G s hR hp hr, fun hp5 => ?_⟩
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hr5, hr7, hr11, hr19⟩ := hcon
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have : Fact r.Prime := ⟨hrp⟩
  have hr2 : r ≠ 2 := fun h => by
    subst h
    exact (Nat.not_even_iff_odd.mpr s.fr.odd_card_E)
      (even_iff_two_dvd.mpr (Nat.mem_primeFactors.mp hr).2.1)
  have hJ : s.p ≠ 3 → JFacts := fun _ => hJF
  have h3 : s.p = 3 → r ≠ 3 ∧ ¬ r ∣ s.q ^ 2 - s.q + 1 := fun h =>
    absurd (hp5.symm.trans h) (by norm_num)
  have h5 : s.p = 5 → r ≠ 7 ∧ r ≠ 11 ∧ r ≠ 19 := fun _ => ⟨hr7, hr11, hr19⟩
  have hrp' : r ≠ s.p := by rw [hp5]; exact hr5
  have hf := s.f_eq_of_p_five hR hp5 hr
  have hqr : s.q % r = 5 % r := by
    have := pow_prime_pow_mod hrp 5 1
    rw [pow_one] at this
    rw [Hyp.q, hp5, hf]
    exact this
  have hq4 : s.q % 4 = 1 := by
    rw [Hyp.q, hp5, Nat.pow_mod]
    norm_num
  have hq1 : 1 ≤ s.q := by omega
  refine s.false_of_odd_torus hJ hR hr hrp' h3 h5 ⟨fun h => by omega, fun _ h => ?_⟩
  have h1 : 1 ≡ s.q [MOD r] := (Nat.modEq_iff_dvd' hq1).mpr h
  have h2 : 1 ≡ 5 [MOD r] := h1.trans hqr
  have h3' := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 5)).mp h2
  exact not_dvd_four hrp hr2 h3'

end CFSG.Walter.W67
