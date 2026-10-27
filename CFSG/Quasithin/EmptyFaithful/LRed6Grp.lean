module

public import CFSG.Quasithin.EmptyFaithful.Insp11L3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace LRed6

section Arith

theorem prime_dvd_1080_mul_two_pow {r a : ℕ} (hr : r.Prime) (h : r ∣ 1080 * 2 ^ a) :
    r = 2 ∨ r = 3 ∨ r = 5 := by
  have h' : r ∣ 2 ^ (a + 3) * 3 ^ 3 * 5 := by
    have e : 1080 * 2 ^ a = 2 ^ (a + 3) * 3 ^ 3 * 5 := by ring
    rwa [e] at h
  rcases (Nat.Prime.dvd_mul hr).mp h' with h1 | h2
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h3 | h4
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h3))
    · exact Or.inr (Or.inl
        ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow h4)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 5)).mp h2))

theorem not_dvd_1080_mul_two_pow {r a : ℕ} (hr : r.Prime) (h7 : r ≠ 2) (h3 : r ≠ 3) (h5 : r ≠ 5) :
    ¬ r ∣ 1080 * 2 ^ a := fun h => by
  rcases prime_dvd_1080_mul_two_pow hr h with h | h | h <;> omega

theorem eq_three_of_cube_dvd {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ 3 ∣ 1080 * 2 ^ a) :
    p = 3 := by
  have hcop : Nat.Coprime (p ^ 3) (2 ^ (a + 3)) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h135 : p ^ 3 ∣ 135 := by
    have e : 1080 * 2 ^ a = 2 ^ (a + 3) * 135 := by ring
    rw [e] at h
    exact hcop.dvd_of_dvd_mul_left h
  have hle : p ^ 3 ≤ 135 := Nat.le_of_dvd (by norm_num) h135
  have hp5 : p ≤ 5 := by
    by_contra hcon
    push Not at hcon
    have : 6 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hcon 3
    omega
  have hp2' := hp.two_le
  interval_cases p
  · exact absurd rfl hp2
  · rfl
  · exact absurd hp (by norm_num)
  · norm_num at h135

end Arith

section Main

theorem partB (D : Type) [Group D] [Finite D] (D₁ D₂ N : Subgroup D)
    (hA : IsGoldschmidtAmalgam D₁ D₂) (hF : F6.F618ConclusionCat D₁ D₂)
    (hO : oTwoUpper (⊤ : Subgroup D) ≤ N) (hnp : oTwoUpper (⊤ : Subgroup D) ≠ ⊤)
    (hhat : F6.IsHatAlt 6 ↥N) : F6.IsHatSym 6 D := by
  classical
  have hperf : Group.IsPerfect ↥N := Group.isPerfect_def.mpr hhat.1.1
  have hNle : N ≤ oTwoUpper (⊤ : Subgroup D) := B1Red.perfect_le_oTwoUpper' le_top hperf
  have hNtop : N ≠ ⊤ := fun h => hnp (le_antisymm le_top (h ▸ hNle))
  have hN1080 : Nat.card ↥N = 1080 := by
    rw [Insp9.card_hatAlt hhat (by norm_num)]
    norm_num [Nat.factorial]
  obtain ⟨a, ha⟩ := Insp11.index_eq_two_pow hO
  have hD : Nat.card D = 1080 * 2 ^ a := by
    rw [← Subgroup.card_mul_index N, hN1080, ha]
  have ha1 : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    subst this
    exact hNtop (Subgroup.index_eq_one.mp (by simpa using ha))
  have h16 : 2 ^ 4 ∣ Nat.card D := by
    rw [hD]
    have e' : 1080 * 2 ^ a = 2 ^ (a + 3) * 135 := by ring
    rw [e']
    exact (Nat.pow_dvd_pow 2 (by omega : 4 ≤ a + 3)).mul_right 135
  have hTk : ∀ k, Nat.card ↥(D₁ ⊓ D₂) = 2 ^ k → 4 ≤ k := fun k hk => by
    by_contra hlt
    exact Insp11.not_two_pow_dvd_of_amalgam hA hk (by omega) h16
  have h7 : ¬ 7 ∣ Nat.card D := by
    rw [hD]
    exact not_dvd_1080_mul_two_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h11 : ¬ 11 ∣ Nat.card D := by
    rw [hD]
    exact not_dvd_1080_mul_two_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h13 : ¬ 13 ∣ Nat.card D := by
    rw [hD]
    exact not_dvd_1080_mul_two_pow (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have h27 : 27 ∣ Nat.card D := by
    rw [hD]
    exact (show 27 ∣ 1080 by norm_num).mul_right _
  have hperm : ∀ n : ℕ, Nat.card (Equiv.Perm (Fin n)) = n.factorial := fun n => by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hpsl : ∀ p : ℕ, p.Prime → (p % 8 = 3 ∨ p % 8 = 5) → F6.IsL2FieldExtCat p D → False := by
    intro p hp hmod hext
    obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hext
    obtain ⟨Kq, -, -, hidx, -, hcard⟩ :=
      Insp9.exists_normal_psl_of_psigma hp (by omega) K hK eK
    have hpK : p ∣ Nat.card ↥Kq := by
      have h2 : p ∣ 2 * Nat.card ↥Kq := ⟨p * ((p ^ 2) ^ 2 - 1), by rw [hcard]; ring⟩
      rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
      · have := Nat.le_of_dvd (by norm_num) h
        omega
      · exact h
    have hpD : p ∣ 1080 * 2 ^ a := hD ▸ hpK.trans (Subgroup.card_subgroup_dvd_card Kq)
    have hp35 : p = 3 ∨ p = 5 := by
      rcases prime_dvd_1080_mul_two_pow hp hpD with h | h | h <;> omega
    rcases hp35 with rfl | rfl
    ·
      have h360 : Nat.card ↥Kq = 360 := by omega
      have hdD : Nat.card ↥Kq * Kq.index = Nat.card D := Subgroup.card_mul_index Kq
      have hD720 : Nat.card D ∣ 720 := by
        rw [← hdD, h360]
        have : Kq.index ∣ 2 := hidx
        have h2 : 360 * Kq.index ∣ 360 * 2 := Nat.mul_dvd_mul_left 360 this
        simpa using h2
      have := h27.trans hD720
      omega
    · have h7800 : Nat.card ↥Kq = 7800 := by omega
      apply h13
      exact (show 13 ∣ 7800 by norm_num).trans (h7800 ▸ Subgroup.card_subgroup_dvd_card Kq)
  have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ → F6.IsF618CaseOrientedCat H₁ H₂ →
      F6.IsHatSym 6 D := by
    intro H₁ H₂ hHH hc
    rcases hc with c | c | c | c | c | c | c | c | c | c | c | c | c
    · exfalso
      have := hTk 1 (by rw [← hHH]; simpa using c.card_inf)
      omega
    · exfalso
      rcases c with he2 | ⟨φ, hφ, hK⟩
      · obtain ⟨e2⟩ := he2
        have h36 : Nat.card D = 36 := by
          rw [Nat.card_congr e2.toEquiv, Nat.card_prod, hperm 3]
          rfl
        rw [hD] at h36
        omega
      · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
          Insp9.card_E4, hK.2.1] at h1
        rw [hD] at h1
        omega
    · exfalso
      have := hTk 3 (by rw [← hHH, c.card_inf]; norm_num)
      omega
    · exfalso
      have := hTk 2 (by rw [← hHH, c.card_inf]; norm_num)
      omega
    · exfalso
      have := hTk 3 (by rw [← hHH, c.card_inf]; norm_num)
      omega
    · exfalso
      have := hTk 3 (by rw [← hHH, c.card_inf]; norm_num)
      omega
    · exfalso
      have := hTk 3 (by rw [← hHH, c.card_inf]; norm_num)
      omega
    · obtain ⟨hD8, -⟩ := c
      rcases hD8 with hH | ⟨p, hp, hmod, hext⟩
      · exact hH
      · exact (hpsl p hp hmod hext).elim
    · exfalso
      obtain ⟨hD9, -⟩ := c
      rcases hD9 with heS | hH | ⟨p, hp, hmod, hext⟩
      · obtain ⟨eS⟩ := heS
        apply h7
        rw [Nat.card_congr eS.toEquiv, hperm 7]
        exact ⟨720, by norm_num [Nat.factorial]⟩
      · apply h7
        rw [Insp11.card_hatSym hH]
        exact ⟨2160, by norm_num [Nat.factorial]⟩
      · exact hpsl p hp (by omega) hext
    · exfalso
      obtain ⟨⟨p, hmod, hS⟩, -⟩ := c
      have hcube := (Insp9.isSLEps3_qs_dvd hS).2
      have hp3 := eq_three_of_cube_dvd hS.1 (by omega) (hD ▸ hcube)
      subst hp3
      apply h7
      rw [Insp9.card_isSLEps3_three hS]
      exact ⟨864, by norm_num⟩
    · exfalso
      obtain ⟨⟨p, hmod, hG⟩, -⟩ := c
      obtain ⟨Kq, -, hS⟩ := Insp9.exists_index_two_isSLEps3 hG
      have hcube := (Insp9.isSLEps3_qs_dvd hS).2.trans (Subgroup.card_subgroup_dvd_card Kq)
      have hp3 := eq_three_of_cube_dvd hS.1 (by omega) (hD ▸ hcube)
      subst hp3
      apply h7
      have h6048 := Insp9.card_isSLEps3_three hS
      exact (show 7 ∣ 6048 by norm_num).trans (h6048 ▸ Subgroup.card_subgroup_dvd_card Kq)
    · exfalso
      obtain ⟨⟨e12⟩, -⟩ := c
      apply h11
      rw [Nat.card_congr e12.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
      exact ⟨8640, by norm_num⟩
    · exfalso
      obtain ⟨⟨e13⟩, -⟩ := c
      have hsimple : IsSimpleGroup ↥CFSG.Blueprint.NativeSporadic.M12 :=
        CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      have hnc : ∃ a b : ↥CFSG.Blueprint.NativeSporadic.M12, a * b ≠ b * a := by
        by_contra hcomm
        push Not at hcomm
        have : IsMulCommutative ↥CFSG.Blueprint.NativeSporadic.M12 :=
          ⟨⟨fun a b => hcomm a b⟩⟩
        have hq : (Nat.card ↥CFSG.Blueprint.NativeSporadic.M12).Prime :=
          IsSimpleGroup.prime_card
        rw [CFSG.Sporadic.Mathieu.card_M12] at hq
        norm_num at hq
      have hcen : Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M12 = ⊥ := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center ↥CFSG.Blueprint.NativeSporadic.M12) with h | h
        · exact h
        · exfalso
          obtain ⟨a, b, hab⟩ := hnc
          exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top a) b).symm)
      have hdvd := Subgroup.card_dvd_of_injective
        (MulAut.conj : ↥CFSG.Blueprint.NativeSporadic.M12 →* MulAut _)
        (Insp9.conj_injective_of_center_eq_bot hcen)
      rw [CFSG.Sporadic.Mathieu.card_M12, ← Nat.card_congr e13.toEquiv] at hdvd
      exact h11 ((show 11 ∣ 95040 by norm_num).trans hdvd)
  rcases hF with hF | hF
  · exact key D₁ D₂ rfl hF
  · exact key D₂ D₁ (inf_comm _ _) hF

end Main

end LRed6

end CFSG.Quasithin
