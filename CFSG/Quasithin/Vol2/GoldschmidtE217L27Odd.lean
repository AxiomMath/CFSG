module

public import CFSG.Quasithin.Vol2.GoldschmidtE217R4L27Inv

public section

namespace CFSG.Quasithin

open E217R4

namespace E217L27

structure L27c (K : Type*) [Group K] : Prop where
  l27 : L27 K
  card : Nat.card K = 168

theorem L27c.of_mulEquiv {K K' : Type*} [Group K] [Group K'] (e : K ≃* K') (h : L27c K') :
    L27c K :=
  ⟨L27.of_mulEquiv e h.l27, by rw [Nat.card_congr e.toEquiv]; exact h.card⟩

theorem l27c_psl {F : Type} [Field F] [Fintype F] (hF7 : Fintype.card F = 7) :
    L27c (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
  ⟨l27_psl hF7, (psl7_basic hF7).2⟩

variable {K : Type*} [Group K]

theorem finite_of_l27c (hK : L27c K) : Finite K :=
  Nat.finite_of_card_ne_zero (by rw [hK.card]; norm_num)

theorem eq_one_or_eight_of_dvd {n : ℕ} (hd : n ∣ 24) (hm : n % 7 = 1) : n = 1 ∨ n = 8 := by
  have hle : n < 25 := by
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have key : ∀ m : Fin 25, (m : ℕ) ∣ 24 → (m : ℕ) % 7 = 1 → (m : ℕ) = 1 ∨ (m : ℕ) = 8 := by
    decide
  exact key ⟨n, hle⟩ hd hm

theorem card_normalizer_seven (hK : L27c K) {P : Subgroup K} (hP : Nat.card P = 7) :
    Nat.card (Subgroup.normalizer (P : Set K)) = 21 := by
  have := finite_of_l27c hK
  have hf7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hfac : (Nat.card K).factorization 7 = 1 := by
    rw [hK.card, show (168 : ℕ) = 7 * 24 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [hf7.out.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 7 ∣ 24)]
  let S : Sylow 7 K := Sylow.ofCard P (by rw [hP, hfac]; norm_num)
  have hS : (S : Subgroup K) = P := rfl
  have hmod : Nat.card (Sylow 7 K) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 K
  have hidx : P.index = 24 := by
    have h1 := Subgroup.card_mul_index P
    rw [hP, hK.card] at h1
    omega
  have hdvd : Nat.card (Sylow 7 K) ∣ P.index := S.card_dvd_index
  rw [hidx] at hdvd
  have hn := eq_one_or_eight_of_dvd hdvd hmod
  have hnorm : Nat.card (Sylow 7 K) = (Subgroup.normalizer (P : Set K)).index :=
    S.card_eq_index_normalizer
  rcases hn with h1 | h8
  · exfalso
    rw [h1] at hnorm
    have htop : Subgroup.normalizer (P : Set K) = ⊤ := Subgroup.index_eq_one.1 hnorm.symm
    have hnormal : P.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact htop
    have := hK.l27.simple
    rcases (haveI := hnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal P) with hb | ht
    · have : Nat.card P = 1 := by rw [hb]; simp
      omega
    · have : Nat.card P = Nat.card K := by
        rw [ht]; exact Subgroup.card_top
      rw [hP, hK.card] at this
      omega
  · rw [h8] at hnorm
    have h1 := Subgroup.card_mul_index (Subgroup.normalizer (P : Set K))
    rw [← hnorm, hK.card] at h1
    omega

theorem mem_normalizer_zpowers_of_inv {y a : K} (hy2 : y * y = 1) (hya : y * a * y⁻¹ = a⁻¹) :
    y ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup K) : Set K) := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hconj : ∀ k : ℤ, y * a ^ k * y⁻¹ = a ^ (-k) := fun k => by
    rw [← conj_zpow, hya, inv_zpow']
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact Subgroup.mem_zpowers_iff.2 ⟨-k, (hconj k).symm⟩
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
    refine Subgroup.mem_zpowers_iff.2 ⟨-k, ?_⟩
    have h' : h = y * a ^ k * y⁻¹ := by
      calc h = y⁻¹ * (y * h * y⁻¹) * y := by group
        _ = y⁻¹ * a ^ k * y := by rw [hk]
        _ = y * a ^ k * y⁻¹ := by rw [hyi]
    rw [h', hconj]

theorem card_eq_three_of_involution (hK : L27c K) {N : Subgroup K} (hN1 : N ≠ ⊥)
    (hNodd : Odd (Nat.card N)) {y : K} (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hyN : y ∈ Subgroup.normalizer (N : Set K)) :
    Nat.card N = 3 ∧ ∀ g ∈ N, y * g * y⁻¹ = g⁻¹ := by
  have := finite_of_l27c hK
  have : Finite N := inferInstance
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hdvd21 : Nat.card N ∣ 21 := by
    have h1 : Nat.card N ∣ 21 * 8 := by
      have := Subgroup.card_subgroup_dvd_card N
      rwa [hK.card] at this
    have hcop : Nat.Coprime (Nat.card N) 8 := by
      have := Nat.Coprime.pow_right 3 (Nat.coprime_two_right.2 hNodd)
      simpa using this
    exact hcop.dvd_of_dvd_mul_right h1
  have hD : N ⊓ Subgroup.centralizer ({y} : Set K) = ⊥ := by
    set D := N ⊓ Subgroup.centralizer ({y} : Set K) with hDdef
    have h1 : Nat.card D ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card D ∣ 8 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : D ≤ Subgroup.centralizer ({y} : Set K))
      rwa [hK.l27.cent2 y hy2 hy1] at this
    have hDodd : Odd (Nat.card D) := Odd.of_dvd_nat hNodd h1
    have h3 : Nat.card D = 1 := by
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (by simpa using h2 : _ ∣ 2 ^ 3)
      rcases k with _ | k
      · simpa using hk'
      · exfalso
        rw [hk', pow_succ] at hDodd
        exact (Nat.not_even_iff_odd.2 hDodd) (even_iff_two_dvd.2 (dvd_mul_left 2 _))
    exact Subgroup.eq_bot_of_card_eq D h3
  have hinv : ∀ g ∈ N, y * g * y⁻¹ = g⁻¹ := by
    let f : N → N := fun n => ⟨(n : K)⁻¹ * (y * n * y⁻¹),
      N.mul_mem (N.inv_mem n.2) ((Subgroup.mem_normalizer_iff.1 hyN n).1 n.2)⟩
    have hinj : Function.Injective f := by
      intro n m hnm
      have h := congrArg Subtype.val hnm
      have h' : (m : K) * (n : K)⁻¹ * y * n = y * m := by
        calc (m : K) * (n : K)⁻¹ * y * n = m * ((n : K)⁻¹ * (y * n * y⁻¹)) * y := by group
          _ = m * ((m : K)⁻¹ * (y * m * y⁻¹)) * y := by
              have h'' : (n : K)⁻¹ * (y * n * y⁻¹) = (m : K)⁻¹ * (y * m * y⁻¹) := h
              rw [h'']
          _ = y * m := by group
      have hc : (m : K) * (n : K)⁻¹ ∈ N ⊓ Subgroup.centralizer ({y} : Set K) := by
        refine ⟨N.mul_mem m.2 (N.inv_mem n.2), ?_⟩
        show (m : K) * (n : K)⁻¹ ∈ Subgroup.centralizer ({y} : Set K)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h3 : y * ((m : K) * (n : K)⁻¹) = ((m : K) * (n : K)⁻¹) * y := by
          calc y * ((m : K) * (n : K)⁻¹) = (y * m) * (n : K)⁻¹ := by group
            _ = ((m : K) * (n : K)⁻¹ * y * n) * (n : K)⁻¹ := by rw [h']
            _ = ((m : K) * (n : K)⁻¹) * y := by group
        exact h3.symm
      rw [hD, Subgroup.mem_bot, mul_inv_eq_one] at hc
      exact Subtype.ext hc.symm
    have hsurj := Finite.injective_iff_surjective.1 hinj
    intro g hg
    obtain ⟨n, hn⟩ := hsurj ⟨g, hg⟩
    have h := congrArg Subtype.val hn
    have h' : (n : K)⁻¹ * (y * n * y⁻¹) = g := h
    rw [← h']
    have hyy' : y⁻¹ * y⁻¹ = 1 := by rw [← mul_inv_rev, hy2, inv_one]
    have e : y * (y * (n : K) * y⁻¹) * y⁻¹ = n := by
      calc y * (y * (n : K) * y⁻¹) * y⁻¹ = (y * y) * n * (y⁻¹ * y⁻¹) := by group
        _ = n := by rw [hy2, hyy']; group
    calc y * ((n : K)⁻¹ * (y * n * y⁻¹)) * y⁻¹
        = (y * (n : K)⁻¹ * y⁻¹) * (y * (y * (n : K) * y⁻¹) * y⁻¹) := by group
      _ = (y * (n : K)⁻¹ * y⁻¹) * n := by rw [e]
      _ = ((n : K)⁻¹ * (y * n * y⁻¹))⁻¹ := by group
  refine ⟨?_, hinv⟩
  by_cases h7 : 7 ∣ Nat.card N
  · exfalso
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := N) 7 h7
    have hao : orderOf (a : K) = 7 := by rw [Subgroup.orderOf_coe]; exact ha
    have hP : Nat.card (Subgroup.zpowers (a : K)) = 7 := by rw [Nat.card_zpowers, hao]
    have hyP := mem_normalizer_zpowers_of_inv hy2 (hinv _ a.2)
    have h21 := card_normalizer_seven hK hP
    have hord : orderOf (⟨y, hyP⟩ : Subgroup.normalizer
        ((Subgroup.zpowers (a : K) : Subgroup K) : Set K)) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by simpa [pow_two] using hy2) hy1
    have := orderOf_dvd_natCard (⟨y, hyP⟩ : Subgroup.normalizer
        ((Subgroup.zpowers (a : K) : Subgroup K) : Set K))
    rw [hord, h21] at this
    omega
  · have hne : Nat.card N ≠ 1 := by
      intro h1
      exact hN1 (Subgroup.eq_bot_of_card_eq N h1)
    have key : ∀ m : Fin 22, (m : ℕ) ∣ 21 → ¬ 7 ∣ (m : ℕ) → (m : ℕ) ≠ 1 → (m : ℕ) = 3 := by
      decide
    have hlt : Nat.card N < 22 := by
      have := Nat.le_of_dvd (by norm_num) hdvd21
      omega
    exact key ⟨Nat.card N, hlt⟩ hdvd21 h7 hne

theorem exists_inv_three (hK : L27c K) {N : Subgroup K} (hN1 : N ≠ ⊥)
    (hNodd : Odd (Nat.card N)) {y : K} (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hyN : y ∈ Subgroup.normalizer (N : Set K)) :
    ∃ a ∈ N, a ^ 3 = 1 ∧ a ≠ 1 ∧ y * a * y⁻¹ = a⁻¹ := by
  have := finite_of_l27c hK
  have : Finite N := inferInstance
  obtain ⟨h3, hinv⟩ := card_eq_three_of_involution hK hN1 hNodd hy2 hy1 hyN
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 (by rw [h3])
  have hao : orderOf (a : K) = 3 := by rw [Subgroup.orderOf_coe]; exact ha
  refine ⟨(a : K), a.2, ?_, ?_, hinv _ a.2⟩
  · rw [← hao]; exact pow_orderOf_eq_one _
  · intro h1
    rw [h1, orderOf_one] at hao
    omega

theorem false_of_order_eight (hK : L27c K) {N : Subgroup K} (hN1 : N ≠ ⊥)
    (hNodd : Odd (Nat.card N)) {D : Subgroup K} (hD : Nat.card D = 8)
    (hDN : D ≤ Subgroup.normalizer (N : Set K)) : False := by
  have := finite_of_l27c hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 (by rw [hD]; norm_num)
  have hyo : orderOf (y : K) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
  have hy2 : (y : K) * y = 1 := by rw [← pow_two, ← hyo]; exact pow_orderOf_eq_one _
  have hy1 : (y : K) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hyo
    omega
  obtain ⟨h3, -⟩ := card_eq_three_of_involution hK hN1 hNodd hy2 hy1 (hDN y.2)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 (by rw [h3])
  have hao : orderOf (a : K) = 3 := by rw [Subgroup.orderOf_coe]; exact ha
  have ha3 : (a : K) ^ 3 = 1 := by rw [← hao]; exact pow_orderOf_eq_one _
  have ha1 : (a : K) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hao
    omega
  let φ : D → N := fun d => ⟨d * a * (d : K)⁻¹, (Subgroup.mem_normalizer_iff.1 (hDN d.2) a).1 a.2⟩
  have hφ : Function.Injective φ := by
    intro d d' hdd'
    have h := congrArg Subtype.val hdd'
    have h' : (d : K) * a * (d : K)⁻¹ = (d' : K) * a * (d' : K)⁻¹ := h
    have hc : (a : K) * ((d' : K)⁻¹ * d) = ((d' : K)⁻¹ * d) * a := by
      have : (d' : K)⁻¹ * ((d : K) * a * (d : K)⁻¹) * d' = a := by
        rw [h']; group
      calc (a : K) * ((d' : K)⁻¹ * d)
          = ((d' : K)⁻¹ * (d * a * (d : K)⁻¹) * d') * ((d' : K)⁻¹ * d) := by rw [this]
        _ = ((d' : K)⁻¹ * d) * a := by group
    obtain ⟨i, hi⟩ := hK.l27.cent3 (a : K) ha3 ha1 ((d' : K)⁻¹ * d) hc.symm
    have he3 : ((d'⁻¹ * d : D) : K) ^ 3 = 1 := by
      have : ((d'⁻¹ * d : D) : K) = (d' : K)⁻¹ * d := rfl
      rw [this, hi, ← pow_mul, mul_comm, pow_mul, ha3, one_pow]
    have he3' : (d'⁻¹ * d : D) ^ 3 = 1 := Subtype.ext (by simpa using he3)
    have h1 : orderOf (d'⁻¹ * d : D) ∣ 3 := orderOf_dvd_of_pow_eq_one he3'
    have h2 : orderOf (d'⁻¹ * d : D) ∣ 8 := hD ▸ orderOf_dvd_natCard _
    have h4 : orderOf (d'⁻¹ * d : D) = 1 :=
      Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 3 8) h1 h2
    have h5 : (d'⁻¹ * d : D) = 1 := orderOf_eq_one_iff.1 h4
    exact (inv_mul_eq_one.1 h5).symm
  have := Nat.card_le_card_of_injective φ hφ
  omega

end E217L27

end CFSG.Quasithin
