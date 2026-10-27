module

public import CFSG.Permutation.SylowTwoNormalizer.Sym

public section

namespace CFSG.Permutation.SylowTwoNormalizer

open Equiv MulAction Subgroup
open scoped Pointwise

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem eq_two_pow_pred_of_two_mul_eq_two_pow {n x : ℕ} (hn : 1 ≤ n)
    (h : 2 * x = 2 ^ n) : x = 2 ^ (n - 1) := by
  have hn' : n = n - 1 + 1 := by omega
  rw [hn', pow_succ, mul_comm (2 ^ (n - 1)) 2] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem restr_inf_stabilizer (R : Subgroup (Perm Ω)) (s : Set Ω) :
    restr R s = restr (R ⊓ stabilizer (Perm Ω) s) s := by
  simp only [restr]
  congr 1
  ext g
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨h, g.2⟩, fun h => h.1⟩

theorem eq_one_of_mem_normalizer_of_isPretransitive (h8 : 8 ≤ Nat.card Ω)
    {R : Subgroup (Perm Ω)} (hRA : R ≤ alternatingGroup Ω) (hR : IsPGroup 2 R)
    (hRi : ¬ 2 ∣ R.relIndex (alternatingGroup Ω)) (htr : MulAction.IsPretransitive R Ω)
    {σ : Perm Ω} (hσ : Odd (orderOf σ)) (hσR : σ ∈ normalizer (R : Set (Perm Ω))) : σ = 1 := by
  classical
  haveI : MulAction.IsPretransitive R Ω := htr
  haveI : Nonempty Ω := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card Ω)).1
  have hdvd : Nat.card Ω ∣ Nat.card R := TauCeti.natCard_dvd_natCard_of_isPretransitive R
  obtain ⟨a, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hdvd.trans (card_dvd_of_isPGroup hR))
  have h8a : 8 ≤ 2 ^ a := by rw [← hn]; exact h8
  have ha3 : 3 ≤ a := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h8a
  have h2a : 2 ≤ 2 ^ a := by omega
  have hX : 1 ≤ 2 ^ (a - 1) := Nat.one_le_two_pow
  have h2a_eq : 2 ^ a = 2 * 2 ^ (a - 1) := by
    rw [← Nat.two_pow_pred_mul_two (by omega : 0 < a), mul_comm]
  have h2 : 2 ≤ Nat.card Ω := by omega
  have hRtwo : 2 * Nat.card R = 2 ^ (2 ^ a - 1) := by
    have h := two_mul_card_eq_of_not_two_dvd_relIndex h2 hRA hR hRi
    rwa [hn, padicValNat_two_factorial_two_pow] at h
  have hRcard : Nat.card R = 2 ^ (2 ^ a - 2) := by
    have h1 := eq_two_pow_pred_of_two_mul_eq_two_pow (n := 2 ^ a - 1) (by omega) hRtwo
    rwa [show 2 ^ a - 1 - 1 = 2 ^ a - 2 by omega] at h1
  obtain ⟨B, hBcard, hRB⟩ := exists_halving_block hR htr (by omega : 2 ≤ Nat.card Ω)
  have hBne' : B.Nonempty := by
    rw [← Set.ncard_pos, ← Nat.card_coe_set_eq]
    omega
  have hBne : B ≠ Bᶜ := ne_compl_self
  have hCcard : 2 * Nat.card ↥(σ • B) = Nat.card Ω := by
    rw [Nat.card_coe_set_eq, Set.ncard_smul_set, ← Nat.card_coe_set_eq, hBcard]
  have hfixB : σ • B = B :=
    smul_set_eq_of_smul_set_eq_or_eq_compl hBne' hσ
      (eq_or_eq_compl_of_halving_of_le_alternatingGroup h8 hRA hR hRi hn hBcard hCcard hRB
        (smul_set_halving_of_mem_normalizer hRB hσR))
  have hσB : σ ∈ stabilizer (Perm Ω) B := MulAction.mem_stabilizer_iff.mpr hfixB
  have hσBc : σ ∈ stabilizer (Perm Ω) Bᶜ := by
    rw [MulAction.mem_stabilizer_iff, Set.smul_set_compl, hfixB]
  set R₀ : Subgroup (Perm Ω) := R ⊓ stabilizer (Perm Ω) B with hR₀def
  have hR₀A : R₀ ≤ alternatingGroup Ω := inf_le_left.trans hRA
  have hR₀ : IsPGroup 2 R₀ := by
    rw [hR₀def]
    exact hR.to_le inf_le_left
  have hg : ∃ g ∈ R, g • B = Bᶜ := exists_smul_eq_compl htr hBcard hBne' hRB
  have hR₀card_two : 2 * Nat.card R₀ = Nat.card R := by
    have h := two_mul_card_inf_stabilizer hRB hg hBne
    simpa [hR₀def] using h
  have hR₀card : Nat.card R₀ = 2 ^ (2 ^ a - 3) := by
    have h1 := eq_two_pow_pred_of_two_mul_eq_two_pow (n := 2 ^ a - 2) (by omega)
      (by rw [hR₀card_two, hRcard])
    rwa [show 2 ^ a - 2 - 1 = 2 ^ a - 3 by omega] at h1
  have hBpow : Nat.card B = 2 ^ (a - 1) :=
    eq_two_pow_pred_of_two_mul_eq_two_pow (n := a) (by omega) (by rw [hBcard, hn])
  have hBcpow : Nat.card ↥Bᶜ = 2 ^ (a - 1) := by
    rw [Nat.card_coe_set_eq, Set.ncard_compl, ← Nat.card_coe_set_eq, hBpow, hn]
    exact Nat.two_pow_sub_two_pow_pred (by omega : 0 < a)
  haveI : Fintype ↥B := Fintype.ofFinite ↥B
  haveI : Fintype ↥Bᶜ := Fintype.ofFinite ↥Bᶜ
  have hpdata : ∃ p ≤ 2 ^ (a - 1) - 1, Nat.card (restr R₀ B) = 2 ^ p := by
    have hdvd : Nat.card (restr R₀ B) ∣ 2 ^ padicValNat 2 (Nat.card ↥B).factorial :=
      card_dvd_of_isPGroup (Ω := ↥B) (isPGroup_restr hR₀ B)
    rw [hBpow, padicValNat_two_factorial_two_pow] at hdvd
    exact (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  obtain ⟨p, hp_le, hpcard⟩ := hpdata
  have hqdata : ∃ q ≤ 2 ^ (a - 1) - 1, Nat.card (restr R₀ Bᶜ) = 2 ^ q := by
    have hdvd : Nat.card (restr R₀ Bᶜ) ∣ 2 ^ padicValNat 2 (Nat.card ↥Bᶜ).factorial :=
      card_dvd_of_isPGroup (Ω := ↥Bᶜ) (isPGroup_restr hR₀ Bᶜ)
    rw [hBcpow, padicValNat_two_factorial_two_pow] at hdvd
    exact (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  obtain ⟨q, hq_le, hqcard⟩ := hqdata
  have hsum_ge : 2 ^ a - 3 ≤ p + q := by
    have hdvd : Nat.card R₀ ∣ Nat.card (restr R₀ B) * Nat.card (restr R₀ Bᶜ) :=
      card_dvd_card_restr_mul (R := R₀) (s := B) inf_le_right
    rw [hR₀card, hpcard, hqcard, ← pow_add] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
  have hsum_le : p + q ≤ 2 * (2 ^ (a - 1) - 1) := by omega
  have hsub : 2 ^ a - 3 = 2 * (2 ^ (a - 1) - 1) - 1 := by omega
  have hcases : p + q = 2 * (2 ^ (a - 1) - 1) - 1 ∨ p + q = 2 * (2 ^ (a - 1) - 1) := by
    omega
  have hboth (hpq : p + q = 2 * (2 ^ (a - 1) - 1)) : σ = 1 := by
    have hpM : p = 2 ^ (a - 1) - 1 := by omega
    have hqM : q = 2 ^ (a - 1) - 1 := by omega
    have hrestrB : restr R B = restr R₀ B := by
      rw [hR₀def]
      exact restr_inf_stabilizer R B
    have hstab : stabilizer (Perm Ω) B = stabilizer (Perm Ω) Bᶜ :=
      (stabilizer_compl (Perm Ω) Ω).symm
    have hrestrBc : restr R Bᶜ = restr R₀ Bᶜ := by
      rw [hR₀def, hstab]
      exact restr_inf_stabilizer R Bᶜ
    have hsylB : ¬ 2 ∣ (restr R₀ B).index := by
      refine not_two_dvd_index_of_dvd_card (Ω := ↥B) (isPGroup_restr hR₀ B) ?_
      rw [hBpow, padicValNat_two_factorial_two_pow, hpcard, hpM]
    have hsylBc : ¬ 2 ∣ (restr R₀ Bᶜ).index := by
      refine not_two_dvd_index_of_dvd_card (Ω := ↥Bᶜ) (isPGroup_restr hR₀ Bᶜ) ?_
      rw [hBcpow, padicValNat_two_factorial_two_pow, hqcard, hqM]
    have hnormB : restrictHom B ⟨σ, hσB⟩ ∈
        normalizer ((restr R₀ B : Subgroup (Perm ↥B)) : Set (Perm ↥B)) := by
      have h := restrictHom_mem_normalizer hσB hσR
      rwa [hrestrB] at h
    have hnormBc : restrictHom Bᶜ ⟨σ, hσBc⟩ ∈
        normalizer ((restr R₀ Bᶜ : Subgroup (Perm ↥Bᶜ)) : Set (Perm ↥Bᶜ)) := by
      have h := restrictHom_mem_normalizer hσBc hσR
      rwa [hrestrBc] at h
    have h1 : restrictHom B ⟨σ, hσB⟩ = 1 :=
      eq_one_of_mem_normalizer (isPGroup_restr hR₀ B) hsylB
        (odd_orderOf_restrictHom hσB hσ) hnormB
    have h2 : restrictHom Bᶜ ⟨σ, hσBc⟩ = 1 :=
      eq_one_of_mem_normalizer (isPGroup_restr hR₀ Bᶜ) hsylBc
        (odd_orderOf_restrictHom hσBc hσ) hnormBc
    exact eq_one_of_restrictHom_eq_one hσB hσBc h1 h2
  have hother (hpq : p + q = 2 * (2 ^ (a - 1) - 1) - 1) : σ = 1 := by
    have hcardmul : Nat.card R₀ = Nat.card (restr R₀ B) * Nat.card (restr R₀ Bᶜ) := by
      rw [hR₀card, hpcard, hqcard, ← pow_add, hpq, hsub]
    have h2B : 2 ≤ Nat.card B := by
      rw [hBpow]
      simpa using (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr
        (by omega : 1 ≤ a - 1)
    have h2Bc : 2 ≤ Nat.card ↥Bᶜ := by
      rw [hBcpow]
      simpa using (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr
        (by omega : 1 ≤ a - 1)
    by_cases hpM : p = 2 ^ (a - 1) - 1
    · have hsylB : ¬ 2 ∣ (restr R₀ B).index := by
        refine not_two_dvd_index_of_dvd_card (Ω := ↥B) (isPGroup_restr hR₀ B) ?_
        rw [hBpow, padicValNat_two_factorial_two_pow, hpcard, hpM]
      exact (false_of_card_eq_mul' (s := B) hR₀A hR₀ inf_le_right h2B hsylB hcardmul).elim
    · have hqM : q = 2 ^ (a - 1) - 1 := by omega
      have hsylBc : ¬ 2 ∣ (restr R₀ Bᶜ).index := by
        refine not_two_dvd_index_of_dvd_card (Ω := ↥Bᶜ) (isPGroup_restr hR₀ Bᶜ) ?_
        rw [hBcpow, padicValNat_two_factorial_two_pow, hqcard, hqM]
      exact (false_of_card_eq_mul (s := B) hR₀A hR₀ inf_le_right h2Bc hsylBc hcardmul).elim
  rcases hcases with hpq | hpq
  · exact hother hpq
  · exact hboth hpq

end CFSG.Permutation.SylowTwoNormalizer
