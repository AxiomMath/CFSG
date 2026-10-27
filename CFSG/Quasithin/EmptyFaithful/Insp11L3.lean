module

public import CFSG.Quasithin.EmptyFaithful.Insp11Defs
public import CFSG.Quasithin.EmptyFaithful.Insp9Cases11
public import CFSG.Quasithin.EmptyFaithful.S153E58C

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Insp11

section Arith

theorem prime_dvd_168_mul_two_pow {r a : ℕ} (hr : r.Prime) (h : r ∣ 168 * 2 ^ a) :
    r = 2 ∨ r = 3 ∨ r = 7 := by
  have h' : r ∣ 2 ^ (a + 3) * 3 * 7 := by
    have e : 168 * 2 ^ a = 2 ^ (a + 3) * 3 * 7 := by ring
    rwa [e] at h
  rcases (Nat.Prime.dvd_mul hr).mp h' with h1 | h2
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h3 | h4
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h3))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h4))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num : Nat.Prime 7)).mp h2))

theorem not_five_dvd (a : ℕ) : ¬ 5 ∣ 168 * 2 ^ a := fun h => by
  rcases prime_dvd_168_mul_two_pow (by norm_num : Nat.Prime 5) h with h | h | h <;> omega

theorem not_cube_dvd {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 3 ∣ 168 * 2 ^ a := by
  intro h
  have hcop : Nat.Coprime (p ^ 3) (2 ^ (a + 3)) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have h21 : p ^ 3 ∣ 21 := by
    have e : 168 * 2 ^ a = 2 ^ (a + 3) * 21 := by ring
    rw [e] at h
    exact hcop.dvd_of_dvd_mul_left h
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have h27 : 27 ≤ p ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left h3 3
  have := Nat.le_of_dvd (by norm_num) h21
  omega

end Arith

section Group

variable {D : Type} [Group D] [Finite D]

theorem index_eq_two_pow {N : Subgroup D} (hO : oTwoUpper (⊤ : Subgroup D) ≤ N) :
    ∃ a : ℕ, N.index = 2 ^ a := by
  classical
  have hi0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hN0 : Nat.card ↥N ≠ 0 := Nat.card_pos.ne'
  refine ⟨N.index.primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd hi0 fun {r} hr hrd => ?_⟩
  by_contra hr2
  have : Fact r.Prime := ⟨hr⟩
  have hodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨R⟩ : Nonempty (Sylow r D) := inferInstance
  have hRN : (R : Subgroup D) ≤ N := by
    intro x hx
    obtain ⟨k, hk⟩ := R.isPGroup' ⟨x, hx⟩
    have hk' : x ^ r ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hord : orderOf x ∣ r ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hodd' : Odd (orderOf x) := Odd.of_dvd_nat (hodd.pow) hord
    exact hO (mem_oTwoUpper_of_odd (Subgroup.mem_top x) hodd')
  have hdvd : Nat.card ↥R ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hRN
  have hcardR : Nat.card ↥R = r ^ (Nat.card D).factorization r := Sylow.card_eq_multiplicity R
  have hmul : Nat.card ↥N * N.index = Nat.card D := Subgroup.card_mul_index N
  have hfac : (Nat.card D).factorization r =
      (Nat.card ↥N).factorization r + N.index.factorization r := by
    rw [← hmul, Nat.factorization_mul hN0 hi0]
    rfl
  have hle : (Nat.card D).factorization r ≤ (Nat.card ↥N).factorization r := by
    rw [hcardR] at hdvd
    exact (hr.pow_dvd_iff_le_factorization hN0).mp hdvd
  have hpos : 0 < N.index.factorization r := hr.factorization_pos_of_dvd hi0 hrd
  omega

omit [Finite D] in
theorem card_hatSym {n : ℕ} (hH : F6.IsHatSym n D) : Nat.card D = 3 * n.factorial := by
  obtain ⟨φ, hφ, hk, -⟩ := hH
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hperm : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hk, hperm] at h1
  rw [h1]
  ring

theorem not_two_pow_dvd_of_amalgam {D₁ D₂ : Subgroup D} (hA : IsGoldschmidtAmalgam D₁ D₂)
    {k m : ℕ} (hT : Nat.card ↥(D₁ ⊓ D₂) = 2 ^ k) (hm : k < m) : ¬ 2 ^ m ∣ Nat.card D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT'⟩ := hA.toIsGoldschmidtTriple.sylow
  have h1 : Nat.card ↥T = 2 ^ (Nat.card D).factorization 2 := Sylow.card_eq_multiplicity T
  have h2 : Nat.card ↥T = Nat.card ↥(D₁ ⊓ D₂) := by rw [← hT']; rfl
  rw [hT] at h2
  have h3 : k = (Nat.card D).factorization 2 :=
    Nat.pow_right_injective le_rfl (h2.symm.trans h1)
  intro hdvd
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.card_pos (α := D)).ne').mp hdvd
  omega

end Group

section Main

theorem inspectL3Normal153 : InspectL3Normal153 := by
  intro D _ _ D₁ D₂ N hA hF hN hO he
  obtain ⟨e⟩ := he
  have hN168 : Nat.card ↥N = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact S153E58.card_statedSL_three_two
  obtain ⟨a, ha⟩ := index_eq_two_pow hO
  have hD : Nat.card D = 168 * 2 ^ a := by
    rw [← Subgroup.card_mul_index N, hN168, ha]
  by_cases ha0 : a = 0
  · subst ha0
    exact Subgroup.index_eq_one.mp (by simpa using ha)
  · exfalso
    have ha1 : 1 ≤ a := Nat.pos_of_ne_zero ha0
    have h16 : 2 ^ 4 ∣ Nat.card D := by
      rw [hD]
      have e' : 168 * 2 ^ a = 2 ^ (a + 3) * 21 := by ring
      rw [e']
      exact (Nat.pow_dvd_pow 2 (by omega : 4 ≤ a + 3)).mul_right 21
    have hTk : ∀ k, Nat.card ↥(D₁ ⊓ D₂) = 2 ^ k → 4 ≤ k := fun k hk => by
      by_contra hlt
      exact not_two_pow_dvd_of_amalgam hA hk (by omega) h16
    have h5 : ¬ 5 ∣ Nat.card D := by
      rw [hD]
      exact not_five_dvd a
    have hperm : ∀ n : ℕ, Nat.card (Equiv.Perm (Fin n)) = n.factorial := fun n => by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    have key : ∀ H₁ H₂ : Subgroup D, H₁ ⊓ H₂ = D₁ ⊓ D₂ →
        F6.IsF618CaseOrientedCat H₁ H₂ → False := by
      intro H₁ H₂ hHH hc
      rcases hc with c | c | c | c | c | c | c | c | c | c | c | c | c
      · have := hTk 1 (by rw [← hHH]; simpa using c.card_inf)
        omega
      · rcases c with he2 | ⟨φ, hφ, hK⟩
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
      · have := hTk 3 (by rw [← hHH, c.card_inf]; norm_num)
        omega
      · have := hTk 2 (by rw [← hHH, c.card_inf]; norm_num)
        omega
      · have := hTk 3 (by rw [← hHH, c.card_inf]; norm_num)
        omega
      · have := hTk 3 (by rw [← hHH, c.card_inf]; norm_num)
        omega
      · have := hTk 3 (by rw [← hHH, c.card_inf]; norm_num)
        omega
      · obtain ⟨hD8, -⟩ := c
        rcases hD8 with hH | ⟨p, hp, hmod, -, K, _, _, hK, ⟨eK⟩⟩
        · apply h5
          rw [card_hatSym hH]
          exact ⟨432, by norm_num [Nat.factorial]⟩
        · obtain ⟨Kq, -, -, -, -, hcard⟩ :=
            Insp9.exists_normal_psl_of_psigma hp (by omega) K hK eK
          have hpK : p ∣ Nat.card ↥Kq := by
            have h2 : p ∣ 2 * Nat.card ↥Kq := ⟨p * ((p ^ 2) ^ 2 - 1), by rw [hcard]; ring⟩
            rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
            · have := Nat.le_of_dvd (by norm_num) h
              omega
            · exact h
          have hpD : p ∣ 168 * 2 ^ a :=
            hD ▸ hpK.trans (Subgroup.card_subgroup_dvd_card Kq)
          have hp3 : p = 3 := by
            rcases prime_dvd_168_mul_two_pow hp hpD with h | h | h <;> omega
          subst hp3
          apply h5
          have h360 : Nat.card ↥Kq = 360 := by omega
          exact (show 5 ∣ 360 by norm_num).trans (h360 ▸ Subgroup.card_subgroup_dvd_card Kq)
      · obtain ⟨hD9, -⟩ := c
        rcases hD9 with heS | hH | ⟨p, hp, hmod, -, K, _, _, hK, ⟨eK⟩⟩
        · obtain ⟨eS⟩ := heS
          apply h5
          rw [Nat.card_congr eS.toEquiv, hperm 7]
          exact ⟨1008, by norm_num [Nat.factorial]⟩
        · apply h5
          rw [card_hatSym hH]
          exact ⟨3024, by norm_num [Nat.factorial]⟩
        · obtain ⟨Kq, -, -, -, -, hcard⟩ :=
            Insp9.exists_normal_psl_of_psigma hp (by omega) K hK eK
          have hpK : p ∣ Nat.card ↥Kq := by
            have h2 : p ∣ 2 * Nat.card ↥Kq := ⟨p * ((p ^ 2) ^ 2 - 1), by rw [hcard]; ring⟩
            rcases (Nat.Prime.dvd_mul hp).mp h2 with h | h
            · have := Nat.le_of_dvd (by norm_num) h
              omega
            · exact h
          have hpD : p ∣ 168 * 2 ^ a :=
            hD ▸ hpK.trans (Subgroup.card_subgroup_dvd_card Kq)
          rcases prime_dvd_168_mul_two_pow hp hpD with h | h | h <;> omega
      · obtain ⟨⟨p, hmod, hS⟩, -⟩ := c
        exact not_cube_dvd hS.1 (by omega) (hD ▸ (Insp9.isSLEps3_qs_dvd hS).2)
      · obtain ⟨⟨p, hmod, hG⟩, -⟩ := c
        obtain ⟨Kq, -, hS⟩ := Insp9.exists_index_two_isSLEps3 hG
        exact not_cube_dvd hS.1 (by omega)
          (hD ▸ (Insp9.isSLEps3_qs_dvd hS).2.trans (Subgroup.card_subgroup_dvd_card Kq))
      · obtain ⟨⟨e12⟩, -⟩ := c
        apply h5
        rw [Nat.card_congr e12.toEquiv, CFSG.Sporadic.Mathieu.card_M12]
        exact ⟨19008, by norm_num⟩
      · obtain ⟨⟨e13⟩, -⟩ := c
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
        exact h5 ((show 5 ∣ 95040 by norm_num).trans hdvd)
    rcases hF with hF | hF
    · exact key D₁ D₂ rfl hF
    · exact key D₂ D₁ (inf_comm _ _) hF

end Main

end Insp11

end CFSG.Quasithin
