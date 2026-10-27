module

import CFSG.Walter.W67.Section4.Prop41A
import CFSG.Walter.W67.Section4.Prop43cA
import CFSG.Walter.W67.W2Cor32A
public import CFSG.Walter.W67.Interface
import CFSG.Walter.W67.W2Lemma26A

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

theorem ree_order_eq {r : ℕ} (hr : Odd r) (hr1 : 1 ≤ r) :
    (r ^ 3 + 1) * r ^ 3 * (r - 1) = 2 * (r * (r ^ 2 - 1) / 2) * r ^ 2 * (r ^ 2 - r + 1) := by
  have h2 : 2 ∣ r * (r ^ 2 - 1) := by
    have : Even (r ^ 2 - 1) := by
      rw [Nat.even_sub (Nat.one_le_pow _ _ hr1)]
      simp [Nat.even_pow, Nat.not_even_iff_odd.mpr hr]
    exact (even_iff_two_dvd.mp this).mul_left _
  rw [Nat.mul_div_cancel' h2]
  have hrr : r ≤ r ^ 2 := Nat.le_self_pow (by norm_num) r
  have hr2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ hr1
  zify [hr1, hrr, hr2]
  ring

theorem factorization_ree {ℓ r : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hr : Odd r) (hr3 : 3 ≤ r)
    (hℓr : ¬ ℓ ∣ r) (hℓq : ¬ ℓ ∣ r ^ 2 - r + 1) :
    ((r ^ 3 + 1) * r ^ 3 * (r - 1)).factorization ℓ =
      (r * (r ^ 2 - 1) / 2).factorization ℓ := by
  have hr1 : 1 ≤ r := by omega
  have hK0 : r * (r ^ 2 - 1) / 2 ≠ 0 := by
    have h1 : 2 ≤ r * (r ^ 2 - 1) := by
      have : 8 ≤ r ^ 2 - 1 := by
        have : 9 ≤ r ^ 2 := by nlinarith
        omega
      nlinarith
    exact (Nat.div_pos h1 (by norm_num)).ne'
  have h2ne : (2 : ℕ) ≠ 0 := by norm_num
  have hr2ne : r ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have hqne : r ^ 2 - r + 1 ≠ 0 := by omega
  rw [ree_order_eq hr hr1, Nat.factorization_mul (Nat.mul_ne_zero (Nat.mul_ne_zero h2ne hK0)
    hr2ne) hqne, Nat.factorization_mul (Nat.mul_ne_zero h2ne hK0) hr2ne,
    Nat.factorization_mul h2ne hK0]
  simp only [Finsupp.add_apply]
  rw [Nat.factorization_eq_zero_of_not_dvd (fun h => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ
      Nat.prime_two).mp h)),
    Nat.factorization_eq_zero_of_not_dvd (fun h => hℓr (hℓ.dvd_of_dvd_pow h)),
    Nat.factorization_eq_zero_of_not_dvd hℓq]
  ring

variable {G : Type} [Group G] [Finite G]

namespace Std

variable (s : Std G)

theorem eX_eq (X : Subgroup G) : s.eX X = Nat.card X := by
  rw [Hyp.eX, s.F_eq_bot, sup_bot_eq, Subgroup.card_bot, Nat.div_one]

theorem q_mod_eq
    {ℓ : ℕ} [Fact ℓ.Prime] {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥)
    (hXℓ : IsPGroup ℓ X) : s.q % ℓ = s.p ^ (s.f / s.eX X) % ℓ := by
  obtain ⟨hdvd, -, -⟩ := lemma_2_6_i G s.toHyp s.fr hXE hX
  obtain ⟨a, ha⟩ := hXℓ.exists_card_eq
  rw [s.eX_eq, ha] at hdvd ⊢
  have hq : s.q = (s.p ^ (s.f / ℓ ^ a)) ^ ℓ ^ a := by
    rw [Hyp.q, ← pow_mul, Nat.div_mul_cancel hdvd]
  rw [hq, pow_prime_pow_mod Fact.out]

theorem factorization_card_L
    (hJ : s.p ≠ 3 → JFacts) (hR : RFacts) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ2 : ℓ ≠ 2)
    (h3 : s.p = 3 → ℓ ≠ 3 ∧ ¬ ℓ ∣ s.q ^ 2 - s.q + 1)
    (h5 : s.p = 5 → ℓ ≠ 7 ∧ ℓ ≠ 11 ∧ ℓ ≠ 19) {X : Subgroup G} (hXE : X ≤ s.fr.E)
    (hX : X ≠ ⊥) (hXℓ : IsPGroup ℓ X) :
    (Nat.card (s.L X)).factorization ℓ = (Nat.card (s.KX X)).factorization ℓ := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨hedvd, ⟨eK⟩, -⟩ := lemma_2_6_i G s.toHyp s.fr hXE hX
  have hLS := s.L_spec X hXE hX
  obtain ⟨K', hJR, -⟩ := hLS.jr
  have hepos : 0 < s.eX X := Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hedvd
    exact s.f_pos.ne' (Nat.eq_zero_of_zero_dvd hedvd)
  have hfe0 : 0 < s.f / s.eX X := Nat.div_pos (Nat.le_of_dvd s.f_pos hedvd) hepos
  obtain ⟨hL', hLp, hLf, -, -⟩ := IsJRSubgroup.nonempty_jrGroup G s.p_ne_two hfe0 hJR
  set r := s.p ^ (s.f / s.eX X) with hr
  have hqL : hL'.q = r := by rw [JRGroup.q, hLp, hLf]
  have hKc : Nat.card (s.KX X) = r * (r ^ 2 - 1) / 2 := PSL2Sub.card_eq eK s.odd_p hfe0
  have hrodd : Odd r := s.odd_p.pow
  have hr1 : 1 ≤ r := Nat.one_le_pow _ _ (Nat.Prime.pos Fact.out)
  have hmod := s.q_mod_eq hXE hX hXℓ
  rw [← hr] at hmod
  have hLc : Nat.card (s.L X) = Nat.card (s.L X) := rfl
  by_cases h5' : hL'.q = 5
  ·
    have hr5 : r = 5 := hqL ▸ h5'
    have hp5 : s.p = 5 := by
      have : s.p ∣ 5 := by
        rw [← hr5, hr]
        exact dvd_pow_self _ hfe0.ne'
      exact (Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp this
    obtain ⟨hJ1, -, -, -, -⟩ := hJ (by rw [hp5]; norm_num) _ hL' h5'
    have hcard : Nat.card (s.L X) = 2 ^ 3 * 3 * 5 * 7 * 11 * 19 := hJ1.2.1
    obtain ⟨h7, h11, h19⟩ := h5 hp5
    rw [hcard, hKc, hr5]
    have e1 : (2 ^ 3 * 3 * 5 * 7 * 11 * 19 : ℕ) = (5 * (5 ^ 2 - 1) / 2) * (2 * 7 * 11 * 19) := by
      norm_num
    rw [e1, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (n := 2 * 7 * 11 * 19), add_zero]
    intro h
    have h' : ℓ ∣ 2 * 7 * 11 * 19 := h
    rcases (Nat.Prime.dvd_mul hℓ).mp h' with h1 | h1
    · rcases (Nat.Prime.dvd_mul hℓ).mp h1 with h2 | h2
      · rcases (Nat.Prime.dvd_mul hℓ).mp h2 with h3' | h3'
        · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h3')
        · exact h7 ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).mp h3')
      · exact h11 ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).mp h2)
    · exact h19 ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).mp h1)
  ·
    obtain ⟨⟨⟨m, hm, hqm⟩, hord, -, hsolv⟩, -, -, -, -, -, -⟩ := hR _ hL' h5'
    have hp3 : s.p = 3 := by
      have h1 : s.p ∣ 3 ^ m := by
        rw [← hqm, hqL, hr]
        exact dvd_pow_self _ hfe0.ne'
      exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp
        ((Fact.out : s.p.Prime).dvd_of_dvd_pow h1)
    obtain ⟨hℓ3, hℓq⟩ := h3 hp3
    have hℓr : ¬ ℓ ∣ r := by
      intro h
      rw [hr, hp3] at h
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).mp (hℓ.dvd_of_dvd_pow h))
    have hℓr2 : ¬ ℓ ∣ r ^ 2 - r + 1 := by
      intro h
      apply hℓq
      have hq1 : s.q ≤ s.q ^ 2 := Nat.le_self_pow (by norm_num) _
      have hr1' : r ≤ r ^ 2 := Nat.le_self_pow (by norm_num) _
      have e1 : (s.q ^ 2 - s.q + 1) % ℓ = (r ^ 2 - r + 1) % ℓ := by
        have h1 : ((s.q ^ 2 - s.q + 1 : ℕ) : ZMod ℓ) = ((r ^ 2 - r + 1 : ℕ) : ZMod ℓ) := by
          have hq' : (s.q : ZMod ℓ) = (r : ZMod ℓ) := (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmod
          push_cast [Nat.cast_sub hq1, Nat.cast_sub hr1']
          rw [hq']
        exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1
      exact Nat.dvd_of_mod_eq_zero (by rw [e1]; exact Nat.mod_eq_zero_of_dvd h)
    rw [hKc]
    by_cases hs : Group.IsSolvable (s.L X)
    · obtain ⟨hq3, h168, -⟩ := hsolv hs
      have hr3 : r = 3 := hqL ▸ hq3
      rw [h168, hr3]
      have e1 : (168 : ℕ) = (3 * (3 ^ 2 - 1) / 2) * 14 := by norm_num
      rw [e1, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd (n := 14), add_zero]
      intro h
      rw [hr3] at hℓr2
      have h' : ℓ ∣ 2 * 7 := h
      rcases (Nat.Prime.dvd_mul hℓ).mp h' with h1 | h1
      · exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1)
      · exact hℓr2 (by norm_num; exact h1)
    · rw [hord hs, hqL]
      have hr3 : 3 ≤ r := by
        rw [← hqL, hqm]
        obtain ⟨k, rfl⟩ := hm
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact factorization_ree hℓ hℓ2 hrodd hr3 hℓr hℓr2

theorem E_le_centralizer
    {X : Subgroup G} (hXE : X ≤ s.fr.E) :
    s.fr.E ≤ Subgroup.centralizer (X : Set G) := fun _ he =>
  Subgroup.mem_centralizer_iff.mpr fun _ hx => s.E_comm (hXE hx) he

theorem normalizer_le_centralizer
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.centralizer (X : Set G) := by
  have hLS := s.L_spec X hXE hX
  rw [hLS.normalizer_eq (by rw [s.F_eq_bot]; exact bot_le)]
  exact sup_le hLS.le_centralizer (s.E_le_centralizer hXE)

theorem card_normalizer_dvd
    {X : Subgroup G} (hXE : X ≤ s.fr.E) (hX : X ≠ ⊥) :
    Nat.card (Subgroup.normalizer (X : Set G)) ∣ Nat.card (s.L X) * Nat.card s.fr.E := by
  have hLS := s.L_spec X hXE hX
  have hNX := hLS.normalizer_eq (by rw [s.F_eq_bot]; exact bot_le)
  obtain ⟨hLN, hLn⟩ := hLS.normal
  have hNL : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (s.L X : Set G) :=
    le_normalizer_of_normal_subgroupOf hLN hLn
  have hEN : s.fr.E ≤ Subgroup.normalizer (X : Set G) :=
    (s.E_le_centralizer hXE).trans (Subgroup.centralizer_le_normalizer _)
  rw [hNX]
  exact Dvd.intro _ (card_sup_mul_card_inf_of_le_normalizer (hEN.trans hNL))

theorem factorization_card_normalizer_le
    (hJ : s.p ≠ 3 → JFacts) (hR : RFacts) {ℓ : ℕ}
    [Fact ℓ.Prime]
    (hℓ2 : ℓ ≠ 2) (h3 : s.p = 3 → ℓ ≠ 3 ∧ ¬ ℓ ∣ s.q ^ 2 - s.q + 1)
    (h5 : s.p = 5 → ℓ ≠ 7 ∧ ℓ ≠ 11 ∧ ℓ ≠ 19) {X : Subgroup G} (hXE : X ≤ s.fr.E)
    (hX : X ≠ ⊥) (hXℓ : IsPGroup ℓ X) :
    (Nat.card (Subgroup.normalizer (X : Set G))).factorization ℓ ≤
      (Nat.card (s.KX X)).factorization ℓ + (Nat.card s.fr.E).factorization ℓ := by
  have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne'
    (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne')).mpr (s.card_normalizer_dvd hXE hX) ℓ
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    s.factorization_card_L hJ hR hℓ2 h3 h5 hXE hX hXℓ] at hle
  exact hle

theorem exists_sylow_E {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ ∣ Nat.card s.fr.E) :
    ∃ P₀ : Subgroup G, P₀ ≤ s.fr.E ∧ IsPGroup ℓ P₀ ∧ P₀ ≠ ⊥ ∧
      Nat.card P₀ = ℓ ^ (Nat.card s.fr.E).factorization ℓ := by
  obtain ⟨Q⟩ : Nonempty (Sylow ℓ s.fr.E) := inferInstance
  have hcard : Nat.card ((Q : Subgroup s.fr.E).map s.fr.E.subtype) =
      ℓ ^ (Nat.card s.fr.E).factorization ℓ := by
    rw [Subgroup.card_map_of_injective s.fr.E.subtype_injective, Q.card_eq_multiplicity]
  refine ⟨(Q : Subgroup s.fr.E).map s.fr.E.subtype, Subgroup.map_subtype_le _,
    Q.isPGroup'.map _, ?_, hcard⟩
  intro h
  rw [h, Subgroup.card_bot] at hcard
  have hpos : 0 < (Nat.card s.fr.E).factorization ℓ :=
    (Nat.Prime.dvd_iff_one_le_factorization Fact.out Nat.card_pos.ne').mp hℓ
  exact absurd hcard.symm (Nat.one_lt_pow hpos.ne' (Nat.Prime.one_lt Fact.out)).ne'

theorem dvd_card_K
    (hJ : s.p ≠ 3 → JFacts) (hR : RFacts) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓσ : ℓ ∈ s.fr.σ)
    (h3 : s.p = 3 → ℓ ≠ 3 ∧ ¬ ℓ ∣ s.q ^ 2 - s.q + 1)
    (h5 : s.p = 5 → ℓ ≠ 7 ∧ ℓ ≠ 11 ∧ ℓ ≠ 19) : ℓ ∣ Nat.card s.K := by
  by_contra hK
  have hℓE : ℓ ∣ Nat.card s.fr.E := (Nat.mem_primeFactors.mp hℓσ).2.1
  have hℓ2 : ℓ ≠ 2 := fun h => by
    subst h
    exact (Nat.not_even_iff_odd.mpr s.fr.odd_card_E) (even_iff_two_dvd.mpr hℓE)
  obtain ⟨P₀, hP₀E, hP₀ℓ, hP₀ne, hP₀card⟩ := s.exists_sylow_E hℓE
  have hfac := s.factorization_card_normalizer_le hJ hR hℓ2 h3 h5 hP₀E hP₀ne hP₀ℓ
  have hK0 : (Nat.card (s.KX P₀)).factorization ℓ = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun h =>
      hK (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  rw [hK0, zero_add] at hfac
  obtain ⟨R, hR⟩ := hP₀ℓ.exists_le_sylow
  have heq : P₀ = R := eq_of_le_of_factorization_le R.isPGroup' hR (by
    rw [hP₀card, Nat.factorization_pow_self Fact.out]
    exact hfac)
  refine false_of_perfect_of_le_centralizer s.perfect hℓ2 R (heq ▸ hP₀ne) ?_
  rw [← heq]
  exact s.normalizer_le_centralizer hP₀E hP₀ne

end Std

end CFSG.Walter.W67
