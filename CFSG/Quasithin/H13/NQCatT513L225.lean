module

public import CFSG.Quasithin.H13.NQCatT513L2p
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2Cardinality

public section

namespace CFSG.Quasithin.H13.NQCat.T513

open CFSG.GorensteinWalter

theorem core_psl2_25 {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5 ^ 2) {D₁ B₁ : Subgroup (PSL2 K)} (T : Sylow 2 (PSL2 K))
    (hDc : IsCyclic D₁) (hDo : Odd (Nat.card D₁))
    (hperm : ∀ t ∈ (T : Subgroup (PSL2 K)), ∀ x ∈ D₁, ∃ x' ∈ D₁,
      ∃ t' ∈ (T : Subgroup (PSL2 K)), t * x = x' * t')
    (hB3 : Nat.card B₁ = 3) (hBD : B₁ ≤ Subgroup.normalizer (D₁ : Set (PSL2 K))) :
    D₁ ≤ B₁ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : IsOddPrimePower (Nat.card K) := ⟨5, 2, by norm_num, by decide, by norm_num, hK⟩
  have hP : Nat.card (PSL2 K) = 7800 := by
    rw [psl2_card_formula K hodd, hK]
    norm_num
  have hT8 : Nat.card (T : Subgroup (PSL2 K)) = 8 := by
    rw [Sylow.card_eq_multiplicity, hP, show (7800 : ℕ) = 2 ^ 3 * 975 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simp
  set m := Nat.card D₁ with hmdef
  have hcop : Nat.Coprime (Nat.card D₁) (Nat.card (T : Subgroup (PSL2 K))) := by
    rw [hT8, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hDo)
  have hH : Nat.card ↥(D₁ ⊔ (T : Subgroup (PSL2 K))) = m * 8 := by
    rw [card_sup_of_perm hperm hcop, hT8]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := D₁)
  have hgo : orderOf (g : PSL2 K) = m := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  have hord : m ∣ 5 ∨ m ∣ 12 ∨ m ∣ 13 := by
    have h := CFSG.Glauberman.Dickson.psl2_orderOf_dvd hK (g : PSL2 K)
    rw [hgo, hK] at h
    norm_num at h
    exact h
  obtain ⟨n, hn⟩ := hDo
  have hm3 : m ∣ 3 := by
    rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hK (D₁ ⊔ (T : Subgroup (PSL2 K)))
      with ⟨m₀, -, hc, -⟩ | ⟨z, hz, hc, -⟩ | ⟨z, -, hz, ⟨eH⟩⟩ | ⟨-, ⟨eA⟩⟩ | ⟨-, ⟨eS⟩⟩ |
        ⟨-, ⟨eA5⟩⟩ | ⟨m₀, t, -, -, -, ht, E, C, -, -, hEc, -, hCc, -, -, -, φ, -, ⟨eSD⟩⟩ |
        ⟨m₀, hm₀, ⟨eL⟩⟩ | ⟨m₀, hm₀, ⟨eG⟩⟩
    · exfalso
      rw [hH] at hc
      have h2 : 2 ∣ 5 ^ m₀ := by rw [← hc]; exact Dvd.intro (m * 4) (by ring)
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (by norm_num : Nat.Prime 5)).mp
        (Nat.prime_two.dvd_of_dvd_pow h2)
      omega
    · exfalso
      rw [hH] at hc
      norm_num at hz
      have h8 : 8 ∣ z := hc ▸ Dvd.intro_left _ rfl
      rcases hz with hz | hz <;> have := h8.trans hz <;> omega
    · have h2z : 2 * z = m * 8 := by
        rw [← hH, Nat.card_congr eH.toEquiv, DihedralGroup.nat_card]
      norm_num at hz
      rcases hz with hz | hz
      · exfalso
        have hz' : z = 4 * m := by omega
        rw [hz'] at hz
        have := Nat.le_of_dvd (by norm_num) hz
        have hm3' : m ≤ 3 := by omega
        interval_cases m <;> omega
      · have hz' : z = 4 * m := by omega
        rw [hz'] at hz
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) (by simpa using hz)
    · exfalso
      have h12 : Nat.card ↥(D₁ ⊔ (T : Subgroup (PSL2 K))) = 12 := by
        rw [Nat.card_congr eA.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        decide
      omega
    · have h24 : Nat.card ↥(D₁ ⊔ (T : Subgroup (PSL2 K))) = 24 := by
        rw [Nat.card_congr eS.toEquiv, Nat.card_perm, Nat.card_fin]
        decide
      have : m = 3 := by omega
      rw [this]
    · exfalso
      have h60 : Nat.card ↥(D₁ ⊔ (T : Subgroup (PSL2 K))) = 60 := by
        rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
        decide
      omega
    · exfalso
      have hcard : Nat.card ↥(D₁ ⊔ (T : Subgroup (PSL2 K))) = Nat.card E * Nat.card C := by
        rw [Nat.card_congr eSD.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
      rw [hH, hEc, hCc] at hcard
      norm_num at ht
      have h8 : 8 ∣ 5 ^ m₀ * t := hcard ▸ Dvd.intro_left _ rfl
      have hcop8 : Nat.Coprime 8 (5 ^ m₀) :=
        Nat.Coprime.pow_right m₀ (by norm_num)
      have := (hcop8.dvd_of_dvd_mul_left h8).trans ht
      omega
    · exfalso
      have hm₀' : m₀ = 1 ∨ m₀ = 2 := by
        have := Nat.le_of_dvd (by norm_num) hm₀
        interval_cases m₀ <;> simp_all
      have hGF : Nat.card (GaloisField 5 m₀) = 5 ^ m₀ :=
        GaloisField.card 5 m₀ (by omega)
      have hcard : m * 8 = 5 ^ m₀ * ((5 ^ m₀) ^ 2 - 1) / 2 := by
        rw [← hH, Nat.card_congr eL.toEquiv]
        have := psl2_card_formula (GaloisField 5 m₀)
          ⟨5, m₀, by norm_num, by decide, by omega, hGF⟩
        rw [hGF] at this
        exact this
      rcases hm₀' with rfl | rfl
      · norm_num at hcard
        have h8 : 8 ∣ 60 := ⟨m, by rw [← hcard, mul_comm]⟩
        norm_num at h8
      · norm_num at hcard
        have : m = 975 := by omega
        rw [this] at hord
        norm_num at hord
    · exfalso
      have hm₀1 : m₀ = 1 := by
        have := Nat.le_of_dvd (by norm_num) hm₀
        rcases Nat.eq_zero_or_pos m₀ with h0 | h0
        · subst h0
          norm_num at hm₀
        · omega
      subst hm₀1
      have hGF : Nat.card (GaloisField 5 1) = 5 := by
        rw [GaloisField.card 5 1 (by norm_num), pow_one]
      have hcard : m * 8 = 120 := by
        rw [← hH, Nat.card_congr eG.toEquiv]
        have := pgl2_card_formula (GaloisField 5 1)
        rw [hGF] at this
        exact this
      have : m = 15 := by omega
      rw [this] at hord
      norm_num at hord
  have hD3 : IsPGroup 3 D₁ := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h1 | h3
    · exact IsPGroup.of_card (n := 0) (by rw [← hmdef, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [← hmdef, h3, pow_one])
  have hB3' : IsPGroup 3 B₁ := IsPGroup.of_card (n := 1) (by rw [hB3, pow_one])
  have hBD3 : IsPGroup 3 ↥(B₁ ⊔ D₁) := IsPGroup.to_sup_of_normal_right' hB3' hD3 hBD
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hBD3
  have hdvd : 3 ^ a ∣ 7800 := by
    rw [← ha, ← hP]
    exact Subgroup.card_subgroup_dvd_card _
  have ha1 : a ≤ 1 := by
    by_contra h
    push Not at h
    have : 3 ^ 2 ∣ 7800 := (Nat.pow_dvd_pow 3 h).trans hdvd
    norm_num at this
  have hle : Nat.card ↥(B₁ ⊔ D₁) ≤ Nat.card B₁ := by
    rw [ha, hB3]
    calc 3 ^ a ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) ha1
      _ = 3 := by norm_num
  have heq : B₁ ⊔ D₁ = B₁ :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left hle).symm
  rw [← heq]
  exact le_sup_right

end CFSG.Quasithin.H13.NQCat.T513
