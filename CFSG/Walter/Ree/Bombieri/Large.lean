module

public import CFSG.Walter.Ree.Bombieri.Stage2
public import CFSG.Walter.Ree.Bombieri.Lemma3
import CFSG.Walter.Ree.Bombieri.Galois

public section

namespace CFSG.Walter.Ree.Bombieri

@[expose] def Rel (m t l lam : ℕ) : Bool → Prop
  | false => (t * l : ℤ) ≡ lam [ZMOD m]
  | true => (t * l + lam : ℤ) ≡ 0 [ZMOD m]

@[expose] def sgnZ : Bool → ℕ → ℤ
  | false, lam => lam
  | true, lam => -(lam : ℤ)

theorem natAbs_sgnZ (neg : Bool) (lam : ℕ) : (sgnZ neg lam).natAbs = lam := by
  cases neg <;> simp [sgnZ]

theorem rel_iff {m t l lam : ℕ} {neg : Bool} :
    Rel m t l lam neg ↔ (t * l : ℤ) ≡ sgnZ neg lam [ZMOD m] := by
  cases neg
  · rfl
  · simp only [Rel, sgnZ, Int.modEq_iff_dvd]
    constructor <;> intro h <;> convert h using 1 <;> ring

theorem exists_rel {m t l lam : ℕ}
    (h : (t * l : ℤ) ≡ lam [ZMOD m] ∨ (t * l + lam : ℤ) ≡ 0 [ZMOD m]) :
    ∃ neg, Rel m t l lam neg := by
  rcases h with h | h
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

theorem rel_lam_ne_zero {m t l lam : ℕ} {neg : Bool} (hcop : Nat.Coprime t m) (hl : 1 ≤ l)
    (hlm : l < m) (h : Rel m t l lam neg) : lam ≠ 0 := by
  rintro rfl
  rw [rel_iff] at h
  have h1 : (m : ℤ) ∣ (t * l : ℤ) := by
    cases neg <;> simpa [sgnZ] using Int.modEq_zero_iff_dvd.mp h
  have h2 : m ∣ l * t := by rw [mul_comm]; exact_mod_cast h1
  have h3 : m ∣ l := hcop.symm.dvd_of_dvd_mul_right h2
  have := Nat.le_of_dvd (by omega) h3
  omega

theorem rel_half {m t l lam : ℕ} {neg : Bool} (hodd : m % 2 = 1)
    (h : Rel m t (2 * l) (2 * lam) neg) : Rel m t l lam neg := by
  rw [rel_iff] at h ⊢
  have h2 : (2 : ℤ) * (t * l) ≡ 2 * sgnZ neg lam [ZMOD m] := by
    convert h using 1
    · push_cast; ring
    · cases neg <;> simp [sgnZ]
  have hg : Int.gcd m 2 = 1 := by
    rw [Int.gcd_comm]
    have : Nat.Coprime 2 m := Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd)
    exact_mod_cast this
  have := Int.ModEq.cancel_left_div_gcd (by omega) h2
  rwa [hg, Nat.cast_one, Int.ediv_one] at this

theorem rel_elim {m t l lam l' lam' : ℕ} {neg neg' : Bool} (h : Rel m t l lam neg)
    (h' : Rel m t l' lam' neg') : (m : ℤ) ∣ l * sgnZ neg' lam' - l' * sgnZ neg lam := by
  rw [rel_iff] at h h'
  have e1 := h.mul_left (l' : ℤ)
  have e2 := h'.mul_left (l : ℤ)
  rw [show (l' : ℤ) * (t * l) = l * (t * l') by ring] at e1
  exact (e1.symm.trans e2).dvd

@[expose] def dPrime (k : ℕ) : ℕ := if k = 0 then 46 else if k = 1 then 28 else 19

@[expose] def degCheck : Bool :=
  (List.range 4).all fun k => (List.range 10).all fun lam => [false, true].all fun neg =>
    (List.range (k + 1)).all fun i => degS k lam neg i + 2 ≤ 3 ^ dPrime k

theorem degCheck_eq : degCheck = true := by decide +kernel

theorem degS_le {k lam : ℕ} {neg : Bool} {i : ℕ} (hk : k ≤ 3) (hlam : lam ≤ 9) (hi : i ≤ k) :
    degS k lam neg i + 2 ≤ 3 ^ dPrime k := by
  have hc := degCheck_eq
  simp only [degCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  exact hc k (by omega) lam (by omega) neg (by cases neg <;> simp) i (by omega)

@[expose] def caseCheck : Bool :=
  (List.range 4).all fun k => (List.range 10).all fun lam => [false, true].all fun neg =>
    lam == 0 || (k % 2 == 1 && lam % 2 == 0) || (k == 1 && lam == 1 && !neg) ||
      stage2Case k lam neg

theorem caseCheck_eq : caseCheck = true := by decide +kernel

theorem stage2Case_of {k lam : ℕ} {neg : Bool} (hk : k ≤ 3) (hlam : lam ≤ 9) (h0 : lam ≠ 0)
    (h2 : ¬ (k % 2 = 1 ∧ lam % 2 = 0)) (h21 : ¬ (k = 1 ∧ lam = 1 ∧ neg = false)) :
    stage2Case k lam neg = true := by
  have hc := caseCheck_eq
  simp only [caseCheck, List.all_eq_true, List.mem_range] at hc
  have := hc k (by omega) lam (by omega) neg (by cases neg <;> simp)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at this
  rcases this with ((h | h) | h) | h
  · exact absurd h h0
  · exact absurd h h2
  · exact absurd ⟨h.1.1, h.1.2, h.2⟩ h21
  · exact h

variable {K : Type*} [Field K] [Fintype K] [CharP K 3]

omit [CharP K 3] in
theorem frob_of_rel_false {m t l lam : ℕ} (hK : Fintype.card K = 3 ^ m) (hlam : lam < m)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3 ^ t) (h : Rel m t l lam false) :
    ∀ x, (σ ^ l) x = x ^ 3 ^ lam := by
  intro x
  have h0 : (t * l : ℤ) ≡ lam [ZMOD m] := h
  have h' : t * l % m = lam % m := Int.natCast_modEq_iff.mp (by exact_mod_cast h0)
  rw [pow_apply_of_eq_frob_pow hσ, pow_three_pow_mod hK, h', Nat.mod_eq_of_lt hlam]

omit [CharP K 3] in
theorem frob_of_rel_true {m t l lam : ℕ} (hK : Fintype.card K = 3 ^ m) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 3 ^ t) (h : Rel m t l lam true) : ∀ y, ((σ ^ l) y) ^ 3 ^ lam = y := by
  intro y
  have h0 : (t * l + lam : ℤ) ≡ 0 [ZMOD m] := h
  have h' : (t * l + lam) % m = 0 % m := Int.natCast_modEq_iff.mp (by exact_mod_cast h0)
  rw [pow_apply_of_eq_frob_pow hσ, ← pow_mul, ← pow_add, pow_three_pow_mod hK, h',
    Nat.zero_mod, pow_zero, pow_one]

theorem three_pow_sub_one_le_degreeOf {m t : ℕ} (hK : Fintype.card K = 3 ^ m) {σ : K ≃+* K}
    (hσ : ∀ x, σ x = x ^ 3 ^ t) {H : MvPolynomial (Fin 1) (ZMod 3)} (hH : H ≠ 0)
    (hvan : ∀ z : K, MvPolynomial.eval₂ (castThree K) (fun i : Fin 1 => (σ ^ (i : ℕ)) z) H = 0) :
    3 ^ m - 1 ≤ H.degreeOf 0 := by
  obtain ⟨α, hα, β, hβ, hne, hmod⟩ := exists_collision (k := 0) hK hσ hH hvan
  have he : ∀ γ : Fin 1 →₀ ℕ, expo t γ = γ 0 := fun γ => by simp [expo]
  rw [he, he] at hmod
  have hne0 : α 0 ≠ β 0 := fun h => hne (Finsupp.ext fun i => by fin_cases i; exact h)
  have h1 := MvPolynomial.monomial_le_degreeOf 0 hα
  have h2 := MvPolynomial.monomial_le_degreeOf 0 hβ
  rcases Nat.lt_or_gt_of_ne hne0 with h | h
  · have hd : 3 ^ m - 1 ∣ β 0 - α 0 := (Nat.modEq_iff_dvd' h.le).mp hmod
    have := Nat.le_of_dvd (by omega) hd
    omega
  · have hd : 3 ^ m - 1 ∣ α 0 - β 0 := (Nat.modEq_iff_dvd' h.le).mp hmod.symm
    have := Nat.le_of_dvd (by omega) hd
    omega

theorem main_step
    {m t : ℕ} (hK : Fintype.card K = 3 ^ m) (hm : 100 ≤ m) (hodd : m % 2 = 1)
    {σ : K ≃+* K} (hσ : ∀ x, σ x = x ^ 3 ^ t) (hcop : Nat.Coprime t m) {a s : ℕ}
    (hB1 : ∀ x : K, (σ x * x) ^ a = x ^ 2) (hB2 : ∀ x : K, (σ x * x ^ 2) ^ s = x)
    (hC : ∀ p ∈ ESigma K σ, thompsonT a p.1 p.2.1 p.2.2 = 0) {l lam : ℕ} {neg : Bool}
    (hl : 1 ≤ l) (hl4 : l ≤ 4) (hlam : lam < 10) (hrel : Rel m t l lam neg)
    (hmin : ∀ l' < l, 1 ≤ l' → ∀ lam' < 10, ∀ neg', ¬ Rel m t l' lam' neg') :
    l = 2 ∧ lam = 1 ∧ neg = false := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have hk3 : k ≤ 3 := by omega
  have hlam0 : lam ≠ 0 := rel_lam_ne_zero hcop hl (by omega) hrel
  have hhalf : ¬ (k % 2 = 1 ∧ lam % 2 = 0) := by
    rintro ⟨hk, hl2⟩
    obtain ⟨k', hk'⟩ : ∃ k', k + 1 = 2 * k' := ⟨(k + 1) / 2, by omega⟩
    obtain ⟨lam', hlam'⟩ : ∃ lam', lam = 2 * lam' := ⟨lam / 2, by omega⟩
    rw [hk', hlam'] at hrel
    exact hmin k' (by omega) (by omega) lam' (by omega) neg (rel_half hodd hrel)
  by_cases hfin : k = 1 ∧ lam = 1 ∧ neg = false
  · obtain ⟨rfl, rfl, rfl⟩ := hfin
    exact ⟨rfl, rfl, rfl⟩
  exfalso
  have hHs := Hs_ne_zero hk3 (by omega) (stage2Case_of hk3 (by omega) hlam0 hhalf hfin)
  have hvan : ∀ z : K, MvPolynomial.eval₂ (castThree K) (fun i : Fin (k + 1) => (σ ^ (i : ℕ)) z)
      (Elim.Hs k lam neg) = 0 := by
    cases neg
    · exact Elim.Hs_vanish_pos hB1 hB2 hC (frob_of_rel_false hK (by omega) hσ hrel)
    · exact Elim.Hs_vanish_neg hB1 hB2 hC (by omega) (frob_of_rel_true hK hσ hrel)
  have hdeg : ∀ i : Fin (k + 1), (Elim.Hs k lam neg).degreeOf i + 2 ≤ 3 ^ dPrime k := fun i =>
    (Nat.add_le_add_right (Elim.degreeOf_Hs_le k lam neg i) 2).trans
      (degS_le hk3 (by omega) (Nat.le_of_lt_succ i.2))
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  ·
    have h1 := three_pow_sub_one_le_degreeOf hK hσ hHs hvan
    have h2 := hdeg 0
    have h3 : 3 ^ 100 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    simp only [dPrime, ite_true] at h2
    have : 3 ^ 46 + 2 ≤ 3 ^ 100 := by norm_num
    omega
  ·
    obtain ⟨l', lam', hl'1, hl'k, hlam', hrel'⟩ := lemma3 hK hσ hk1 hHs hdeg hvan
    obtain ⟨neg', hrel'⟩ := exists_rel hrel'
    have hN := rel_elim hrel hrel'
    have hN0 : ((k + 1 : ℕ) : ℤ) * sgnZ neg' lam' - l' * sgnZ neg lam = 0 := by
      refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hN ?_
      rw [Int.natAbs_natCast]
      calc _ ≤ (((k + 1 : ℕ) : ℤ) * sgnZ neg' lam').natAbs + ((l' : ℤ) * sgnZ neg lam).natAbs :=
            Int.natAbs_sub_le _ _
        _ = (k + 1) * lam' + l' * lam := by
            rw [Int.natAbs_mul, Int.natAbs_mul, natAbs_sgnZ, natAbs_sgnZ, Int.natAbs_natCast,
              Int.natAbs_natCast]
        _ < m := by
            have h1 : l' * lam ≤ k * 9 := Nat.mul_le_mul hl'k (by omega)
            have h2 : (k + 1) * lam' ≤ (k + 1) * (dPrime k - 1) :=
              Nat.mul_le_mul_left _ (by omega)
            interval_cases k <;> simp only [dPrime] at h2 <;> norm_num at h2 <;> omega
    have heq : (k + 1) * lam' = l' * lam := by
      have := congrArg Int.natAbs (sub_eq_zero.mp hN0)
      rwa [Int.natAbs_mul, Int.natAbs_mul, natAbs_sgnZ, natAbs_sgnZ, Int.natAbs_natCast,
        Int.natAbs_natCast] at this
    have hlam'10 : lam' < 10 := by
      by_contra hc
      have h1 : (k + 1) * 10 ≤ (k + 1) * lam' := Nat.mul_le_mul_left _ (by omega)
      have h2 : l' * lam ≤ k * 9 := Nat.mul_le_mul hl'k (by omega)
      omega
    exact hmin l' (by omega) hl'1 lam' hlam'10 neg' hrel'

theorem sq_eq_frob_of_hundred_le
    {m : ℕ} (hK : Fintype.card K = 3 ^ m) (hm : 100 ≤ m)
    (hodd : m % 2 = 1) {σ : K ≃+* K} (hσ : IsThompsonAut K σ) : ∀ x, σ (σ x) = x ^ 3 := by
  classical
  obtain ⟨hA, a, s, -, -, hB1, hB2, hC⟩ := hσ
  obtain ⟨t, -, hσt⟩ := exists_eq_frob_pow hK σ
  have hcop := coprime_of_generates hK (by omega) hσt hA
  have hex : ∃ l, 1 ≤ l ∧ l ≤ 4 ∧ ∃ lam < 10, ∃ neg, Rel m t l lam neg := by
    obtain ⟨l, lam, hl1, hl4, hlam, hrel⟩ := lemma3 (k := 4) (d := 10) hK hσt (by norm_num)
      Elim.H_ne_zero
      (fun i => (Nat.add_le_add_right (Elim.H_degreeOf i) 2).trans
        (by fin_cases i <;> norm_num [Elim.dH]))
      (fun z => by
        have := Elim.lemma2 hB1 hB2 hC z
        rwa [Elim.evA5_eq, MvPolynomial.coe_eval₂Hom] at this)
    obtain ⟨neg, hrel⟩ := exists_rel hrel
    exact ⟨l, hl1, hl4, lam, hlam, neg, hrel⟩
  have hex' : ∃ l, 1 ≤ l ∧ ∃ lam < 10, ∃ neg, Rel m t l lam neg := by
    obtain ⟨l, h1, -, h3⟩ := hex
    exact ⟨l, h1, h3⟩
  obtain ⟨hl1, lam, hlam, neg, hrel⟩ := Nat.find_spec hex'
  have hl4 : Nat.find hex' ≤ 4 := by
    obtain ⟨l, h1, h4, h3⟩ := hex
    exact (Nat.find_min' hex' ⟨h1, h3⟩).trans h4
  have hmin : ∀ l' < Nat.find hex', 1 ≤ l' → ∀ lam' < 10, ∀ neg', ¬ Rel m t l' lam' neg' :=
    fun l' hl' h1 lam' hlam' neg' hr => Nat.find_min hex' hl' ⟨h1, lam', hlam', neg', hr⟩
  obtain ⟨h2, h1, hf⟩ := main_step hK hm hodd hσt hcop hB1 hB2 hC hl1 hl4 hlam hrel hmin
  rw [h2, h1, hf] at hrel
  intro x
  have := frob_of_rel_false hK (by omega) hσt hrel x
  rwa [pow_two, RingAut.mul_apply, pow_one] at this

end CFSG.Walter.Ree.Bombieri
