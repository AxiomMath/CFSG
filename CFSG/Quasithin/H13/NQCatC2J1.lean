module

public import CFSG.Quasithin.H13.NQCatC2JH
public import CFSG.Quasithin.H13.NQCatC2Syl
public import CFSG.Quasithin.H13.NQCatT513L2p
public import CFSG.Quasithin.H13.NQCatC2Gen

public section

namespace CFSG.Quasithin.H13.NQCat.C2

open CFSG.Walter.J1 CFSG.QuasithinUnique CFSG.Quasithin.H13.NQCat.T513
open scoped Pointwise

variable {A : Type} [Group A]

theorem comm_of_isCyclic {C : Subgroup A} (hC : IsCyclic ↥C) {a b : A} (ha : a ∈ C)
    (hb : b ∈ C) : a * b = b * a := by
  obtain ⟨g, hg⟩ := hC.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨a, ha⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨b, hb⟩)
  have := (Commute.zpow_zpow_self g i j).eq
  rw [hi, hj] at this
  exact congrArg Subtype.val this

theorem false_of_cube_mul {T : Subgroup A} (hT : IsPGroup 2 ↥T) {y t : A}
    (hyN : y ∈ Subgroup.normalizer (T : Set A)) (hy3 : y ^ 3 = 1) (ht : t ∈ T)
    (hw : orderOf (y * t) = 7) : False := by
  have hc : ∀ u ∈ T, y⁻¹ * u * y ∈ T := by
    intro u hu
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyN) u).mp hu
    rwa [inv_inv] at this
  have h3 : (y * t) ^ 3 = (y⁻¹ * (y⁻¹ * t * y) * y) * (y⁻¹ * t * y) * t := by
    have e : (y * t) ^ 3 = y ^ 3 * ((y⁻¹ * (y⁻¹ * t * y) * y) * (y⁻¹ * t * y) * t) := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [e, hy3, one_mul]
  have hmem : (y * t) ^ 3 ∈ T := by
    rw [h3]
    exact mul_mem (mul_mem (hc _ (hc t ht)) (hc t ht)) ht
  have ho : orderOf ((y * t) ^ 3) = 7 := by
    rw [Nat.Coprime.orderOf_pow (by rw [hw]; norm_num), hw]
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hT ⟨_, hmem⟩
  rw [Subgroup.orderOf_mk, ho] at hk
  rcases k with _ | k
  · norm_num at hk
  · rw [pow_succ] at hk
    omega

variable [Finite A] {Q : Subgroup A} (hJ : JankoHyp ↥Q)
include hJ

theorem le_normalizer_of_perm {T C : Subgroup A} (hT : IsSylowTwoOf T Q) (hCQ : C ≤ Q)
    (hCc : IsCyclic ↥C) (hCo : Odd (Nat.card C))
    (hperm : ∀ t ∈ T, ∀ x ∈ C, ∃ x' ∈ C, ∃ t' ∈ T, t * x = x' * t') :
    C ≤ Subgroup.normalizer (T : Set A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT8 := card_of_sylow hJ hT
  set m := Nat.card C with hm
  have hm0 : m ≠ 0 := Nat.card_pos.ne'
  have hcop : Nat.Coprime (Nat.card C) (Nat.card T) := by
    rw [hT8, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hCo)
  have hH : Nat.card ↥(C ⊔ T) = m * 8 := by rw [card_sup_of_perm hperm hcop, hT8]
  have hHset := coe_sup_of_perm hperm
  have hHQ : C ⊔ T ≤ Q := sup_le hCQ hT.1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have hgo : orderOf (g : A) = m := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg]
  have hpow : ∀ {d : ℕ}, d ∣ m → orderOf ((g : A) ^ (m / d)) = d := fun hd => by
    rw [← hgo]
    exact orderOf_pow_orderOf_div (by rw [hgo]; exact hm0) (by rw [hgo]; exact hd)
  have hgQ : ∀ k : ℕ, (g : A) ^ k ∈ Q := fun k => hCQ (C.pow_mem g.2 k)
  have hprime : ∀ p : ℕ, p.Prime → p ∣ m → p = 3 ∨ p = 7 := by
    intro p hp hpm
    by_contra hne
    have : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hCo) (even_iff_two_dvd.mpr hpm)
    set q := p ^ m.factorization p with hq
    have hqm : q ∣ m := Nat.ordProj_dvd m p
    have hk1 : 1 ≤ m.factorization p := (hp.dvd_iff_one_le_factorization hm0).mp hpm
    have hq1 : 1 < q := Nat.one_lt_pow (by omega) hp.one_lt
    set P := Subgroup.zpowers ((g : A) ^ (m / q)) with hP
    have hPq : Nat.card P = q := by rw [Nat.card_zpowers, hpow hqm]
    have hPC : P ≤ C := Subgroup.zpowers_le.mpr (C.pow_mem g.2 _)
    have hCP : C ≤ Subgroup.normalizer (P : Set A) :=
      le_normalizer_of_forall_comm fun a ha b hb => comm_of_isCyclic hCc (hPC ha) hb
    have hPH : P ≤ C ⊔ T := hPC.trans le_sup_left
    have hP'card : Nat.card ↥(P.subgroupOf (C ⊔ T)) = q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv, hPq]
    have hP'p : IsPGroup p ↥(P.subgroupOf (C ⊔ T)) := IsPGroup.of_card hP'card
    have hP'i : ¬ p ∣ (P.subgroupOf (C ⊔ T)).index := by
      have h1 := Subgroup.card_mul_index (P.subgroupOf (C ⊔ T))
      rw [hP'card, hH] at h1
      have h2 : (P.subgroupOf (C ⊔ T)).index = m / q * 8 := by
        apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (by omega : q ≠ 0))
        rw [h1, ← mul_assoc, Nat.mul_div_cancel' hqm]
      rw [h2]
      intro hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3
      · exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_ordCompl hp hm0) h3
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 3 by simpa using h3)))
    let PS : Sylow p ↥(C ⊔ T) := hP'p.toSylow hP'i
    have hmod := card_sylow_modEq_one p ↥(C ⊔ T)
    rw [Sylow.card_eq_index_normalizer PS] at hmod
    have hCN : C.subgroupOf (C ⊔ T) ≤
        Subgroup.normalizer (PS : Set ↥(C ⊔ T)) := by
      intro c hc
      rw [Subgroup.mem_subgroupOf] at hc
      show c ∈ Subgroup.normalizer ((PS : Subgroup ↥(C ⊔ T)) : Set ↥(C ⊔ T))
      rw [Subgroup.mem_normalizer_iff]
      intro x
      exact Subgroup.mem_normalizer_iff.mp (hCP hc) x
    have hCi : (C.subgroupOf (C ⊔ T)).index = 8 := by
      have h1 := Subgroup.card_mul_index (C.subgroupOf (C ⊔ T))
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hH] at h1
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm0) h1
    have hdvd : (Subgroup.normalizer (PS : Set ↥(C ⊔ T))).index ∣ 2 ^ 3 := by
      have h := Subgroup.index_dvd_of_le hCN
      rw [hCi] at h
      norm_num
      exact h
    have hn1 : (Subgroup.normalizer (PS : Set ↥(C ⊔ T))).index = 1 := by
      obtain ⟨i, hi3, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hpd := (Nat.modEq_iff_dvd' (by rw [hi]; exact Nat.one_le_two_pow)).mp hmod.symm
      rw [hi] at hpd ⊢
      interval_cases i
      · rfl
      · exfalso
        norm_num at hpd
        exact hp.one_lt.ne' hpd
      · exfalso
        norm_num at hpd
        exact hne (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpd))
      · exfalso
        norm_num at hpd
        exact hne (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpd))
    have hnorm := Subgroup.index_eq_one.mp hn1
    have hTP : T ≤ Subgroup.normalizer (P : Set A) := by
      intro t ht
      apply mem_normalizer_of_conj_mem'
      intro x hx
      have h1 : (⟨t, Subgroup.mem_sup_right ht⟩ : ↥(C ⊔ T)) ∈
          Subgroup.normalizer (PS : Set ↥(C ⊔ T)) := by
        rw [hnorm]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_normalizer_iff.mp h1 ⟨x, hPH hx⟩).mp hx
    have hPo : Odd (Nat.card P) := Odd.of_dvd_nat hCo (Subgroup.card_dvd_of_le hPC)
    have hPb := eq_bot_of_le_normalizer hJ hT (hPC.trans hCQ) hPo hTP
    rw [hPb, Subgroup.card_bot] at hPq
    omega
  have h21 : ¬ 21 ∣ m := by
    intro h21
    exact false_of_seven_three hJ (hgQ _) (hgQ _) (hpow ((by norm_num : 7 ∣ 21).trans h21))
      (hpow ((by norm_num : 3 ∣ 21).trans h21)) (by rw [← pow_add, ← pow_add, add_comm])
  have hm21 : m ∣ 21 := by
    have hmQ : m ∣ 175560 := hJ.card_eq ▸ Subgroup.card_dvd_of_le hCQ
    have hnd : ∀ p : ℕ, p.Prime → p ≠ 3 → p ≠ 7 → Nat.Coprime m p := fun p hp h3 h7 =>
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hpm => by
        rcases hprime p hp hpm with h | h
        · exact h3 h
        · exact h7 h)
    have h2 : Nat.Coprime m 2 := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      fun h => (Nat.not_even_iff_odd.mpr hCo) (even_iff_two_dvd.mpr h))
    have hc : Nat.Coprime m (2 ^ 3 * 5 * 11 * 19) :=
      (((h2.pow_right 3).mul_right (hnd 5 (by norm_num) (by norm_num) (by norm_num))).mul_right
        (hnd 11 (by norm_num) (by norm_num) (by norm_num))).mul_right
        (hnd 19 (by norm_num) (by norm_num) (by norm_num))
    exact hc.dvd_of_dvd_mul_right (by simpa using hmQ)
  have hm3 : m = 1 ∨ m = 3 ∨ m = 7 := by
    have hmem : m ∈ Nat.divisors 21 := Nat.mem_divisors.mpr ⟨hm21, by norm_num⟩
    rw [show Nat.divisors 21 = {1, 3, 7, 21} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact absurd (by rw [h] : 21 ∣ m) h21
  rcases hm3 with hm1 | hmp
  · rw [Subgroup.eq_bot_of_card_eq C hm1]
    exact bot_le
  have hmp' : m.Prime := by rcases hmp with h | h <;> rw [h] <;> norm_num
  by_contra hCN
  have hCNT : ∀ c ∈ C, c ∈ Subgroup.normalizer (T : Set A) → c = 1 := by
    intro c hc hcN
    by_contra hc1
    apply hCN
    have hco : orderOf c = m := by
      rcases (Nat.dvd_prime hmp').mp (Subgroup.orderOf_dvd_natCard C hc) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hc1
      · exact h
    have hCeq : Subgroup.zpowers c = C :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hc) (by rw [Nat.card_zpowers, hco])
    rw [← hCeq, Subgroup.zpowers_le]
    exact hcN
  obtain ⟨O, hOH, hON, -, hOcard, hOodd⟩ := exists_odd_complement (K := C ⊔ T) (T := T)
    le_sup_right hT.2.1 (fun R hRK hR2 hTR => hT.eq_of_le hTR (hRK.trans hHQ) hR2) (by
      intro n hn hnN x hx
      have hn' : n ∈ ((C ⊔ T : Subgroup A) : Set A) := hn
      rw [hHset] at hn'
      obtain ⟨c, hc, t, ht, hct⟩ := hn'
      have hct' : c * t = n := hct
      subst hct'
      have hcN : c ∈ Subgroup.normalizer (T : Set A) := by
        have := mul_mem hnN (inv_mem (Subgroup.le_normalizer ht))
        rwa [mul_inv_cancel_right] at this
      rw [hCNT c hc hcN, one_mul]
      exact comm_of_mem_sylow hJ hT ht hx)
  have hOm : Nat.card O = m := by
    rw [hT8, hH] at hOcard
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) hOcard
  have hCO : C ≤ O := fun c hc => hOodd c (Subgroup.mem_sup_left hc)
    (Odd.of_dvd_nat hCo (Subgroup.orderOf_dvd_natCard C hc))
  have hCeq : C = O := Subgroup.eq_of_le_of_card_ge hCO hOm.le
  have hTC : T ≤ Subgroup.normalizer (C : Set A) := by
    intro t ht
    apply mem_normalizer_of_conj_mem'
    intro c hc
    have := hON.conj_mem ⟨c, hOH (hCO hc)⟩ (Subgroup.mem_subgroupOf.mpr (hCO hc))
      ⟨t, Subgroup.mem_sup_right ht⟩
    rw [hCeq]
    exact this
  have hCb := eq_bot_of_le_normalizer hJ hT hCQ hCo hTC
  rw [hCb, Subgroup.card_bot] at hm
  rcases hmp with h | h <;> omega

end CFSG.Quasithin.H13.NQCat.C2
