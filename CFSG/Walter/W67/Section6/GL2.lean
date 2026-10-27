module

public import CFSG.Adapters.FrobeniusKernel
public import CFSG.Walter.W67.Section5.Sylow52
public import CFSG.Walter.JRFacts

public section

namespace CFSG.Walter.W67.Sec6

open scoped Pointwise

section Involutions

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem four_dvd_of_involutions {A : Subgroup Γ} {a b : Γ} (ha : a ∈ A) (hb : b ∈ A)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b = b * a) (hne : a ≠ b) :
    4 ∣ Nat.card A := by
  have hN : Subgroup.zpowers b ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_left hab n).eq
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_bot]
    rcases CFSG.Walter.eq_one_or_eq_of_mem_zpowers ha2 hxa with h | h
    · exact h
    rcases CFSG.Walter.eq_one_or_eq_of_mem_zpowers hb2 hxb with h' | h'
    · exact h'
    exact absurd (h.symm.trans h') hne
  have h := Sec52.card_sup_mul_card_inf hN
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ha2, hb2] at h
  have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers a ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr hb) (Subgroup.zpowers_le.mpr ha)
  have := Subgroup.card_dvd_of_le hle
  rwa [h] at this

theorem eq_of_involutions {A : Subgroup Γ} (hA2 : (Nat.card A).factorization 2 ≤ 1) {a b : Γ}
    (ha : a ∈ A) (hb : b ∈ A) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2)
    (hab : a * b = b * a) : a = b := by
  by_contra hne
  have h4 := four_dvd_of_involutions ha hb ha2 hb2 hab hne
  have : 2 ≤ (Nat.card A).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
      (by norm_num at h4 ⊢; exact h4)
  omega

theorem odd_orderOf_mul_of_involutions {A : Subgroup Γ} (hA2 : (Nat.card A).factorization 2 ≤ 1)
    {a b : Γ} (ha : a ∈ A) (hb : b ∈ A) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) :
    Odd (orderOf (a * b)) := by
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨n, hn⟩ := hev
  set w := a * b with hw
  have hpos : 0 < orderOf w := orderOf_pos w
  have hn0 : n ≠ 0 := by omega
  have hz2 : orderOf (w ^ n) = 2 := by
    rw [orderOf_pow' w hn0, hn, Nat.gcd_eq_right ⟨2, by ring⟩]
    exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hn0) (by ring)
  have haw : a * w * a⁻¹ = w⁻¹ := by
    rw [hw, hainv, mul_inv_rev, hainv, hbinv]
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [haa, one_mul]
  have haz : a * w ^ n = w ^ n * a := by
    have h1 : a * w ^ n * a⁻¹ = (w ^ n)⁻¹ := by
      rw [← conj_pow, haw, inv_pow]
    have h2 : (w ^ n)⁻¹ = w ^ n := by
      have : w ^ n * w ^ n = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
      exact inv_eq_of_mul_eq_one_right this
    calc a * w ^ n = a * w ^ n * a⁻¹ * a := by group
      _ = w ^ n * a := by rw [h1, h2]
  have hzA : w ^ n ∈ A := A.pow_mem (A.mul_mem ha hb) n
  have hza := eq_of_involutions hA2 ha hzA ha2 hz2 haz
  have haw' : a * w = w * a := by
    rw [hza]
    exact (Commute.self_pow w n).eq.symm
  have hab : a * b = b * a := by
    have h1 : a * (a * b) = (a * b) * a := haw'
    calc a * b = a⁻¹ * (a * (a * b)) := by group
      _ = a⁻¹ * ((a * b) * a) := by rw [h1]
      _ = (a * a) * b * a := by rw [hainv]; group
      _ = b * a := by rw [haa, one_mul]
  have heq := eq_of_involutions hA2 ha hb ha2 hb2 hab
  have hw1 : w = 1 := by rw [hw, ← heq, haa]
  rw [hw1, orderOf_one] at hn
  omega

end Involutions

namespace GL2

variable {r : ℕ} [hr : Fact r.Prime]

@[expose] def ent (a : GL (Fin 2) (ZMod r)) (i j : Fin 2) : ZMod r :=
  (a : Matrix (Fin 2) (Fin 2) (ZMod r)) i j

theorem ent_mul (a b : GL (Fin 2) (ZMod r)) (i j : Fin 2) :
    ent (a * b) i j = ent a i 0 * ent b 0 j + ent a i 1 * ent b 1 j := by
  simp only [ent, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem ent_one_00 : ent (1 : GL (Fin 2) (ZMod r)) 0 0 = 1 := by
  simp [ent]

theorem ent_one_01 : ent (1 : GL (Fin 2) (ZMod r)) 0 1 = 0 := by
  simp [ent]

theorem ent_one_10 : ent (1 : GL (Fin 2) (ZMod r)) 1 0 = 0 := by
  simp [ent]

theorem ent_one_11 : ent (1 : GL (Fin 2) (ZMod r)) 1 1 = 1 := by
  simp [ent]

theorem ext' {a b : GL (Fin 2) (ZMod r)} (h00 : ent a 0 0 = ent b 0 0)
    (h01 : ent a 0 1 = ent b 0 1) (h10 : ent a 1 0 = ent b 1 0) (h11 : ent a 1 1 = ent b 1 1) :
    a = b := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

theorem eq_one_iff' {a : GL (Fin 2) (ZMod r)} :
    a = 1 ↔ ent a 0 0 = 1 ∧ ent a 0 1 = 0 ∧ ent a 1 0 = 0 ∧ ent a 1 1 = 1 := by
  constructor
  · rintro rfl
    exact ⟨ent_one_00, ent_one_01, ent_one_10, ent_one_11⟩
  · rintro ⟨h00, h01, h10, h11⟩
    exact ext' (by rw [h00, ent_one_00]) (by rw [h01, ent_one_01]) (by rw [h10, ent_one_10])
      (by rw [h11, ent_one_11])

theorem det_eq (a : GL (Fin 2) (ZMod r)) :
    ((Matrix.GeneralLinearGroup.det a : (ZMod r)ˣ) : ZMod r) =
      ent a 0 0 * ent a 1 1 - ent a 0 1 * ent a 1 0 := by
  simp only [Matrix.GeneralLinearGroup.val_det_apply, ent, Matrix.det_fin_two]

theorem upper_mul {a b : GL (Fin 2) (ZMod r)} (ha : ent a 1 0 = 0) (hb : ent b 1 0 = 0) :
    ent (a * b) 1 0 = 0 ∧ ent (a * b) 0 0 = ent a 0 0 * ent b 0 0 ∧
      ent (a * b) 1 1 = ent a 1 1 * ent b 1 1 := by
  simp only [ent_mul, ha, hb]
  refine ⟨by ring, by ring, by ring⟩

theorem lower_mul {a b : GL (Fin 2) (ZMod r)} (ha : ent a 0 1 = 0) (hb : ent b 0 1 = 0) :
    ent (a * b) 0 1 = 0 ∧ ent (a * b) 0 0 = ent a 0 0 * ent b 0 0 ∧
      ent (a * b) 1 1 = ent a 1 1 * ent b 1 1 := by
  simp only [ent_mul, ha, hb]
  refine ⟨by ring, by ring, by ring⟩

theorem upper_inv {a : GL (Fin 2) (ZMod r)} (ha : ent a 1 0 = 0) :
    ent a⁻¹ 1 0 = 0 ∧ ent a 0 0 * ent a⁻¹ 0 0 = 1 ∧ ent a 1 1 * ent a⁻¹ 1 1 = 1 := by
  have h1 := eq_one_iff'.mp (mul_inv_cancel a)
  simp only [ent_mul, ha, zero_mul, zero_add] at h1
  obtain ⟨h1a, -, h1c, h1d⟩ := h1
  have h11 : ent a 1 1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1d
    exact zero_ne_one h1d
  have hb : ent a⁻¹ 1 0 = 0 := by
    rcases mul_eq_zero.mp h1c with h | h
    · exact absurd h h11
    · exact h
  refine ⟨hb, ?_, h1d⟩
  rw [hb, mul_zero, add_zero] at h1a
  exact h1a

theorem lower_inv {a : GL (Fin 2) (ZMod r)} (ha : ent a 0 1 = 0) :
    ent a⁻¹ 0 1 = 0 ∧ ent a 0 0 * ent a⁻¹ 0 0 = 1 ∧ ent a 1 1 * ent a⁻¹ 1 1 = 1 := by
  have h1 := eq_one_iff'.mp (mul_inv_cancel a)
  simp only [ent_mul, ha, zero_mul, add_zero] at h1
  obtain ⟨h1a, h1b, -, h1d⟩ := h1
  have h00 : ent a 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at h1a
    exact zero_ne_one h1a
  have hb : ent a⁻¹ 0 1 = 0 := by
    rcases mul_eq_zero.mp h1b with h | h
    · exact absurd h h00
    · exact h
  refine ⟨hb, h1a, ?_⟩
  rw [hb, mul_zero, zero_add] at h1d
  exact h1d

theorem unipotent_pow {a : GL (Fin 2) (ZMod r)} (h10 : ent a 1 0 = 0) (h00 : ent a 0 0 = 1)
    (h11 : ent a 1 1 = 1) (n : ℕ) :
    ent (a ^ n) 0 0 = 1 ∧ ent (a ^ n) 0 1 = n * ent a 0 1 ∧ ent (a ^ n) 1 0 = 0 ∧
      ent (a ^ n) 1 1 = 1 := by
  induction n with
  | zero => simp [ent_one_00, ent_one_01, ent_one_10, ent_one_11]
  | succ n ih =>
    obtain ⟨i00, i01, i10, i11⟩ := ih
    rw [pow_succ]
    simp only [ent_mul, i00, i01, i10, i11, h10, h00, h11]
    push_cast
    refine ⟨by ring, by ring, by ring, by ring⟩

theorem lower_pow {a : GL (Fin 2) (ZMod r)} (h01 : ent a 0 1 = 0) (h11 : ent a 1 1 = ent a 0 0)
    (n : ℕ) :
    ent (a ^ n) 0 0 = ent a 0 0 ^ n ∧ ent (a ^ n) 0 1 = 0 ∧
      ent (a ^ n) 1 0 * ent a 0 0 = n * ent a 0 0 ^ n * ent a 1 0 ∧
      ent (a ^ n) 1 1 = ent a 0 0 ^ n := by
  induction n with
  | zero => simp [ent_one_00, ent_one_01, ent_one_10, ent_one_11]
  | succ n ih =>
    obtain ⟨i00, i01, i10, i11⟩ := ih
    rw [pow_succ]
    simp only [ent_mul, i00, i01, i11, h01, h11]
    refine ⟨by ring, by ring, ?_, by ring⟩
    push_cast
    linear_combination (ent a 0 0) * i10

theorem diag_pow {a : GL (Fin 2) (ZMod r)} (h01 : ent a 0 1 = 0) (h10 : ent a 1 0 = 0)
    (n : ℕ) :
    ent (a ^ n) 0 0 = ent a 0 0 ^ n ∧ ent (a ^ n) 0 1 = 0 ∧ ent (a ^ n) 1 0 = 0 ∧
      ent (a ^ n) 1 1 = ent a 1 1 ^ n := by
  induction n with
  | zero => simp [ent_one_00, ent_one_01, ent_one_10, ent_one_11]
  | succ n ih =>
    obtain ⟨i00, i01, i10, i11⟩ := ih
    rw [pow_succ]
    simp only [ent_mul, i00, i01, i10, i11, h01, h10]
    refine ⟨by ring, by ring, by ring, by ring⟩

theorem eq_one_of_pow_r {A : Subgroup (GL (Fin 2) (ZMod r))} (hA : Nat.Coprime r (Nat.card A))
    {a : GL (Fin 2) (ZMod r)} (ha : a ∈ A) (har : a ^ r = 1) : a = 1 := by
  have h1 : orderOf a ∣ r := orderOf_dvd_of_pow_eq_one har
  have h2 : orderOf a ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A ha
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hA) h2)

theorem two_ne_zero' (hr2 : r ≠ 2) : (2 : ZMod r) ≠ 0 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h2
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact (Fact.out : r.Prime).one_lt.ne' h
  · exact hr2 h

theorem diag_of_coprime (hr2 : r ≠ 2) {A : Subgroup (GL (Fin 2) (ZMod r))}
    (hA : Nat.Coprime r (Nat.card A)) (hA2 : (Nat.card A).factorization 2 ≤ 1)
    {t δ : GL (Fin 2) (ZMod r)} (htA : t ∈ A) (hδA : δ ∈ A)
    (ht00 : ent t 0 0 = 1) (ht01 : ent t 0 1 = 0) (ht10 : ent t 1 0 = 0)
    (ht11 : ent t 1 1 + 1 = 0)
    {k : ZMod r} (hδ00 : ent δ 0 0 = 1) (hδ01 : ent δ 0 1 = 0) (hδ10 : ent δ 1 0 = 0)
    (hδ11 : ent δ 1 1 = k) (hk : k ≠ 1) (hδo : Odd (orderOf δ)) :
    ∀ a ∈ A, ent a 0 1 = 0 ∧ ent a 1 0 = 0 := by
  have h2ne := two_ne_zero' hr2
  set e := ent t 1 1 with he
  have he2 : e * e = 1 := by linear_combination (e - 1) * ht11
  have he1 : e ≠ 1 := by
    intro h
    apply h2ne
    linear_combination ht11 - h
  have h1e : 1 - e = 2 := by linear_combination -ht11
  have ht1 : t ≠ 1 := fun h => he1 (by rw [he, h, ent_one_11])
  have htt : t * t = 1 := eq_one_iff'.mpr (by
    simp only [ent_mul, ht00, ht01, ht10, ← he]
    refine ⟨by ring, by ring, by ring, by linear_combination he2⟩)
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two, htt]) ht1
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨m, hm⟩ := hδo
  have hkm : k ^ (2 * m + 1) = 1 := by
    have h1 := pow_orderOf_eq_one δ
    rw [hm] at h1
    have h2 := (diag_pow hδ01 hδ10 (2 * m + 1)).2.2.2
    rw [h1, ent_one_11, hδ11] at h2
    exact h2.symm
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hkm
    exact zero_ne_one hkm
  have hkn1 : k + 1 ≠ 0 := by
    intro h
    have hkk : k * k = 1 := by linear_combination (k - 1) * h
    have : k ^ (2 * m + 1) = k := by
      rw [pow_succ, pow_mul, sq, hkk, one_pow, one_mul]
    rw [this] at hkm
    exact hk hkm
  have hk2 : k ^ 2 ≠ 1 := by
    intro h
    have : (k - 1) * (k + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact hk (sub_eq_zero.mp h')
    · exact hkn1 h'
  obtain ⟨hδi01, hδi00, hδi11⟩ := lower_inv hδ01
  have hδi10 : ent δ⁻¹ 1 0 = 0 := (upper_inv hδ10).1
  rw [hδ00, one_mul] at hδi00
  rw [hδ11] at hδi11
  have step1 : ∀ a ∈ A, ent a 1 0 = 0 → ent a 0 1 = 0 := by
    intro a ha ha10
    obtain ⟨hai10, hai00, hai11⟩ := upper_inv ha10
    set c := a * δ * a⁻¹ * δ⁻¹ with hc
    have hcA : c ∈ A := A.mul_mem (A.mul_mem (A.mul_mem ha hδA) (A.inv_mem ha)) (A.inv_mem hδA)
    obtain ⟨h1a, h1b, h1c⟩ := upper_mul ha10 hδ10
    obtain ⟨h2a, h2b, h2c⟩ := upper_mul h1a hai10
    obtain ⟨h3a, h3b, h3c⟩ := upper_mul h2a hδi10
    have hc00 : ent c 0 0 = 1 := by
      rw [hc, h3b, h2b, h1b, hδ00, hδi00, mul_one, mul_one, hai00]
    have hc11 : ent c 1 1 = 1 := by
      rw [hc, h3c, h2c, h1c, hδ11]
      linear_combination (k * ent δ⁻¹ 1 1) * hai11 + hδi11
    have hc1 : c = 1 := eq_one_of_pow_r hA hcA (by
      obtain ⟨i00, i01, i10, i11⟩ := unipotent_pow h3a hc00 hc11 r
      rw [ZMod.natCast_self, zero_mul] at i01
      exact eq_one_iff'.mpr ⟨i00, i01, i10, i11⟩)
    have hcomm : a * δ = δ * a := by
      have : a * δ * a⁻¹ * δ⁻¹ = 1 := hc1
      calc a * δ = a * δ * a⁻¹ * δ⁻¹ * (δ * a) := by group
        _ = δ * a := by rw [this, one_mul]
    have h01 := congrArg (fun x => ent x 0 1) hcomm
    simp only [ent_mul, hδ00, hδ01, hδ11] at h01
    have : ent a 0 1 * (k - 1) = 0 := by linear_combination h01
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hk
  have step2 : ∀ a ∈ A, ent a 0 0 ≠ 0 := by
    intro a ha ha00
    have hinv := eq_one_iff'.mp (inv_mul_cancel a)
    simp only [ent_mul, ha00, mul_zero, zero_add] at hinv
    have ha10 : ent a 1 0 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hinv
      exact zero_ne_one hinv.1
    set u := a * t * a⁻¹ with hu
    have huA : u ∈ A := A.mul_mem (A.mul_mem ha htA) (A.inv_mem ha)
    have huo : orderOf u = 2 := by rw [hu, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hto]
    have hua : u * a = a * t := by rw [hu]; group
    have h00 := congrArg (fun x => ent x 0 0) hua
    have h10 := congrArg (fun x => ent x 1 0) hua
    simp only [ent_mul, ha00, ht00, ht10, mul_zero, zero_add, add_zero, mul_one] at h00 h10
    have hu01 : ent u 0 1 = 0 := by
      rcases mul_eq_zero.mp h00 with h | h
      · exact h
      · exact absurd h ha10
    have hu11 : ent u 1 1 = 1 := by
      have : (ent u 1 1 - 1) * ent a 1 0 = 0 := by linear_combination h10
      rcases mul_eq_zero.mp this with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h ha10
    set w := t * u with hw
    have hw01 : ent w 0 1 = 0 := by
      rw [hw, ent_mul, ht00, ht01, hu01]; ring
    have hw11 : ent w 1 1 = e := by
      rw [hw, ent_mul, ht10, ← he, hu01, hu11]; ring
    have hwo := odd_orderOf_mul_of_involutions hA2 htA huA hto huo
    obtain ⟨n, hn⟩ := hwo
    have hpow : ∀ j : ℕ, ent (w ^ j) 0 1 = 0 ∧ ent (w ^ j) 1 1 = e ^ j := by
      intro j
      induction j with
      | zero => exact ⟨ent_one_01, by rw [pow_zero, pow_zero, ent_one_11]⟩
      | succ j ih =>
        obtain ⟨h1, -, h2⟩ := lower_mul ih.1 hw01
        rw [pow_succ]
        refine ⟨h1, ?_⟩
        rw [h2, ih.2, hw11, pow_succ]
    have h1 := (hpow (orderOf w)).2
    rw [pow_orderOf_eq_one, ent_one_11, hn, pow_succ, pow_mul, sq, he2, one_pow, one_mul] at h1
    exact he1 h1.symm
  have step3 : ∀ h ∈ A, ∀ g ∈ A, ent h 1 0 = 0 → ent (g⁻¹ * h * g) 1 0 = 0 →
      ent g 1 0 ≠ 0 → ent h 0 1 = 0 ∧ ent h 0 0 = ent h 1 1 := by
    intro h hh g hg hh10 hb10 hg10
    have hh01 := step1 h hh hh10
    refine ⟨hh01, ?_⟩
    set b := g⁻¹ * h * g with hb
    have hgb : g * b = h * g := by rw [hb]; group
    have e00 := congrArg (fun x => ent x 0 0) hgb
    have e10 := congrArg (fun x => ent x 1 0) hgb
    simp only [ent_mul, hb10, hh01, hh10, mul_zero, add_zero, zero_mul, zero_add] at e00 e10
    have hg00 := step2 g hg
    have h1 : ent b 0 0 = ent h 0 0 := by
      have : (ent b 0 0 - ent h 0 0) * ent g 0 0 = 0 := by linear_combination e00
      rcases mul_eq_zero.mp this with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' hg00
    have h2 : ent b 0 0 = ent h 1 1 := by
      have : (ent b 0 0 - ent h 1 1) * ent g 1 0 = 0 := by linear_combination e10
      rcases mul_eq_zero.mp this with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' hg10
    rw [← h1, h2]
  set A₂ := Subgroup.closure {x | ∃ a ∈ A, x = a * t * a⁻¹} with hA₂
  have hA₂A : A₂ ≤ A := by
    rw [hA₂, Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    exact A.mul_mem (A.mul_mem ha htA) (A.inv_mem ha)
  have htA₂ : t ∈ A₂ := Subgroup.subset_closure ⟨1, A.one_mem, by group⟩
  have hdet : ∀ x ∈ A₂, ((Matrix.GeneralLinearGroup.det x : (ZMod r)ˣ) : ZMod r) ^ 2 = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      have hdt : ((Matrix.GeneralLinearGroup.det t : (ZMod r)ˣ) : ZMod r) = e := by
        rw [det_eq t, ht00, ht01, ht10, ← he]
        ring
      have hc : Matrix.GeneralLinearGroup.det (a * t * a⁻¹) =
          Matrix.GeneralLinearGroup.det t := by
        rw [map_mul, map_mul, map_inv, mul_comm (Matrix.GeneralLinearGroup.det a), mul_assoc,
          mul_inv_cancel, mul_one]
      rw [hc, hdt, sq, he2]
    | one => simp
    | mul x y _ _ hx hy =>
      rw [map_mul, Units.val_mul, mul_pow, hx, hy, one_mul]
    | inv x _ hx =>
      have h1 : ((Matrix.GeneralLinearGroup.det x⁻¹ : (ZMod r)ˣ) : ZMod r) *
          ((Matrix.GeneralLinearGroup.det x : (ZMod r)ˣ) : ZMod r) = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      have h2 := congrArg (fun u : ZMod r => u ^ 2) h1
      simp only [mul_pow, hx, mul_one, one_pow] at h2
      exact h2
  have hscalar : ∀ x ∈ A₂, ent x 0 1 = 0 → ent x 1 0 = 0 → ent x 0 0 = ent x 1 1 → x = 1 := by
    intro x hx h01 h10 heq
    have hxA := hA₂A hx
    have hxc : ∀ y : GL (Fin 2) (ZMod r), x * y = y * x := by
      intro y
      apply ext' <;> simp only [ent_mul, h01, h10, heq] <;> ring
    have hxo : Odd (orderOf x) := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨n, hn⟩ := hev
      have hn0 : n ≠ 0 := by
        intro h
        rw [h] at hn
        exact (orderOf_pos x).ne' hn
      have hz2 : orderOf (x ^ n) = 2 := by
        rw [orderOf_pow' x hn0, hn, Nat.gcd_eq_right ⟨2, by ring⟩]
        exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hn0) (by ring)
      have hzt := eq_of_involutions hA2 (A.pow_mem hxA n) htA hz2 hto
        ((Commute.pow_left (show Commute x t from hxc t) n).eq)
      obtain ⟨i00, -, -, i11⟩ := diag_pow h01 h10 n
      have h3 : ent (x ^ n) 0 0 = ent (x ^ n) 1 1 := by rw [i00, i11, heq]
      rw [hzt, ht00, ← he] at h3
      exact he1 h3.symm
    obtain ⟨m, hm⟩ := hxo
    set c := ent x 0 0 with hcdef
    have hcm : c ^ (2 * m + 1) = 1 := by
      have h1 := pow_orderOf_eq_one x
      rw [hm] at h1
      have h2 := (diag_pow h01 h10 (2 * m + 1)).1
      rw [h1, ent_one_00] at h2
      exact h2.symm
    have hc4 : c ^ 4 = 1 := by
      have h := hdet x hx
      rw [det_eq, h01, h10, ← heq, ← hcdef] at h
      have : (c * c - 0 * 0) ^ 2 = c ^ 4 := by ring
      rw [this] at h
      exact h
    have hc1 : c = 1 := by
      have h : c ^ Nat.gcd (2 * m + 1) 4 = 1 := pow_gcd_eq_one.mpr ⟨hcm, hc4⟩
      have hg : Nat.gcd (2 * m + 1) 4 = 1 := by
        have h2 : Nat.Coprime (2 * m + 1) 2 := by
          rw [Nat.coprime_two_right]
          exact ⟨m, rfl⟩
        have := Nat.Coprime.pow_right 2 h2
        simpa using this
      rw [hg, pow_one] at h
      exact h
    exact eq_one_iff'.mpr ⟨hc1, h01, h10, by rw [← heq]; exact hc1⟩
  let H : Subgroup A₂ :=
    { carrier := {x | ent (x : GL (Fin 2) (ZMod r)) 1 0 = 0}
      one_mem' := ent_one_10
      mul_mem' := fun {x y} hx hy => (upper_mul hx hy).1
      inv_mem' := fun {x} hx => (upper_inv hx).1 }
  have hmemH : ∀ x : A₂, x ∈ H ↔ ent (x : GL (Fin 2) (ZMod r)) 1 0 = 0 := fun x => Iff.rfl
  have hcommt : ∀ y : GL (Fin 2) (ZMod r), t * y = y * t → ent y 0 1 = 0 ∧ ent y 1 0 = 0 := by
    intro y hy
    have e01 := congrArg (fun x => ent x 0 1) hy
    have e10 := congrArg (fun x => ent x 1 0) hy
    simp only [ent_mul, ht00, ht01, ht10, ← he] at e01 e10
    refine ⟨?_, ?_⟩
    · have : 2 * ent y 0 1 = 0 := by linear_combination e01 - ent y 0 1 * h1e
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2ne
      · exact h
    · have : 2 * ent y 1 0 = 0 := by linear_combination -e10 - ent y 1 0 * h1e
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h2ne
      · exact h
  have hfinal : H = ⊤ → ∀ a ∈ A, ent a 0 1 = 0 ∧ ent a 1 0 = 0 := by
    intro hHtop a ha
    have hu : a * t * a⁻¹ ∈ A₂ := Subgroup.subset_closure ⟨a, ha, rfl⟩
    have hu10 : ent (a * t * a⁻¹) 1 0 = 0 :=
      (hmemH ⟨_, hu⟩).mp (hHtop ▸ Subgroup.mem_top _)
    have hu01 := step1 _ (hA₂A hu) hu10
    have hcomm : (a * t * a⁻¹) * t = t * (a * t * a⁻¹) := by
      apply ext' <;> simp only [ent_mul, hu01, hu10, ht00, ht01, ht10] <;> ring
    have heq := eq_of_involutions hA2 (hA₂A hu) htA
      (by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hto]) hto hcomm
    have hat : t * a = a * t := by
      calc t * a = (a * t * a⁻¹) * a := by rw [heq]
        _ = a * t := by group
    exact hcommt a hat
  apply hfinal
  by_contra hHtop
  have hconj : ∀ g x : A₂, x ∈ MulAut.conj g • H ↔ g⁻¹ * x * g ∈ H := by
    intro g x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, ← map_inv,
      MulAut.conj_apply, inv_inv]
  have hH1 : H ≠ ⊥ := by
    intro h
    have : (⟨t, htA₂⟩ : A₂) ∈ H := ht10
    rw [h, Subgroup.mem_bot] at this
    exact ht1 (congrArg Subtype.val this)
  have hfrob : ∀ g : A₂, g ∉ H → H ⊓ (MulAut.conj g • H) = ⊥ := by
    intro g hg
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxH, hxg⟩ := Subgroup.mem_inf.mp hx
    rw [hconj] at hxg
    rw [Subgroup.mem_bot]
    have hg10 : ent (g : GL (Fin 2) (ZMod r)) 1 0 ≠ 0 := hg
    obtain ⟨h01, heq⟩ := step3 x (hA₂A x.2) g (hA₂A g.2) hxH hxg hg10
    exact Subtype.ext (hscalar x x.2 h01 hxH heq)
  obtain ⟨K, hKset, hKn, -, hKH, hKcard⟩ := CFSG.Adapters.frobenius_kernel H hH1 hHtop hfrob
  have hKmem : ∀ x : A₂, x ∈ K ↔ x = 1 ∨ ∀ g : A₂, x ∉ MulAut.conj g • H := by
    intro x
    have : x ∈ (K : Set A₂) ↔ x ∈ ({1} ∪ (Set.univ \ ⋃ g : A₂,
        ((MulAut.conj g • H : Subgroup A₂) : Set A₂)) : Set A₂) := by rw [hKset]
    simp only [SetLike.mem_coe, Set.mem_union, Set.mem_singleton_iff, Set.mem_sdiff,
      Set.mem_univ, Set.mem_iUnion, true_and, not_exists] at this
    exact this
  have hidx : H.index ≠ 1 := fun h => hHtop (Subgroup.index_eq_one.mp h)
  obtain ⟨κ, hκK, hκ1⟩ : ∃ κ ∈ K, κ ≠ 1 := by
    by_contra h
    push Not at h
    have : K = ⊥ := eq_bot_iff.mpr fun x hx => (Subgroup.mem_bot).mpr (h x hx)
    rw [this, Subgroup.card_bot] at hKcard
    exact hidx hKcard.symm
  set t' : A₂ := ⟨t, htA₂⟩ with ht'
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht't'
  let σ : K →* K :=
    { toFun := fun x => ⟨t' * x * t'⁻¹, hKn.conj_mem _ x.2 t'⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun x y => by apply Subtype.ext; simp only [Subgroup.coe_mul]; group }
  have hσinv : Function.Involutive σ := by
    intro x
    apply Subtype.ext
    change t' * (t' * x * t'⁻¹) * t'⁻¹ = x
    rw [ht'inv]
    calc t' * (t' * x * t') * t' = (t' * t') * x * (t' * t') := by group
      _ = x := by rw [ht't']; group
  have hσfp : MonoidHom.FixedPointFree σ := by
    intro x hx
    have hxt : t' * (x : A₂) * t'⁻¹ = x := congrArg Subtype.val hx
    have hxt' : t * ((x : A₂) : GL (Fin 2) (ZMod r)) =
        ((x : A₂) : GL (Fin 2) (ZMod r)) * t := by
      have h1 := congrArg Subtype.val hxt
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht', htinv] at h1
      calc t * ((x : A₂) : GL (Fin 2) (ZMod r)) =
          t * ((x : A₂) : GL (Fin 2) (ZMod r)) * t * t := by rw [mul_assoc _ t t, htt, mul_one]
        _ = ((x : A₂) : GL (Fin 2) (ZMod r)) * t := by rw [h1]
    have hx10 : ent ((x : A₂) : GL (Fin 2) (ZMod r)) 1 0 = 0 := (hcommt _ hxt').2
    have hxKH : (x : A₂) ∈ K ⊓ H := Subgroup.mem_inf.mpr ⟨x.2, hx10⟩
    rw [hKH, Subgroup.mem_bot] at hxKH
    exact Subtype.ext hxKH
  have hσκ : t' * κ * t'⁻¹ = κ⁻¹ := by
    have := congrFun (hσfp.coe_eq_inv_of_involutive hσinv) ⟨κ, hκK⟩
    exact congrArg Subtype.val this
  have hKcomm : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hσfp.commute_all_of_involutive hσinv ⟨x, hx⟩ ⟨y, hy⟩).eq
  have hA₂n : ∀ a ∈ A, ∀ x ∈ A₂, a * x * a⁻¹ ∈ A₂ := by
    intro a ha x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      exact Subgroup.subset_closure ⟨a * b, A.mul_mem ha hb, by group⟩
    | one => simp [A₂.one_mem]
    | mul x y _ _ hx hy =>
      have e' : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      rw [e']
      exact A₂.mul_mem hx hy
    | inv x _ hx =>
      have e' : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
      rw [e']
      exact A₂.inv_mem hx
  have hδinvA : δ⁻¹ ∈ A := A.inv_mem hδA
  set κ' : A₂ := ⟨δ * (κ : GL (Fin 2) (ZMod r)) * δ⁻¹, hA₂n δ hδA _ κ.2⟩ with hκ'
  have hκ'K : κ' ∈ K := by
    rw [hKmem]
    by_cases h1 : κ' = 1
    · exact Or.inl h1
    right
    intro g hg
    rw [hconj] at hg
    set g' : A₂ := ⟨δ⁻¹ * (g : GL (Fin 2) (ZMod r)) * δ, by
      have := hA₂n δ⁻¹ hδinvA _ g.2
      rwa [inv_inv] at this⟩ with hg'
    have hκg : κ ∈ MulAut.conj g' • H := by
      rw [hconj]
      have hgκ : ent (((g⁻¹ * κ' * g : A₂)) : GL (Fin 2) (ZMod r)) 1 0 = 0 := hg
      change ent (((g'⁻¹ * κ * g' : A₂)) : GL (Fin 2) (ZMod r)) 1 0 = 0
      have e' : ((g'⁻¹ * κ * g' : A₂) : GL (Fin 2) (ZMod r)) =
          δ⁻¹ * ((g⁻¹ * κ' * g : A₂) : GL (Fin 2) (ZMod r)) * δ := by
        simp only [hg', hκ', Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e']
      obtain ⟨h1a, -, -⟩ := upper_mul hδi10 hgκ
      exact (upper_mul h1a hδ10).1
    rcases (hKmem κ).mp hκK with h | h
    · exact hκ1 h
    · exact h g' hκg
  have hcomm := hKcomm κ hκK κ' hκ'K
  have hκH : κ ∉ H := by
    intro h
    have : κ ∈ K ⊓ H := Subgroup.mem_inf.mpr ⟨hκK, h⟩
    rw [hKH, Subgroup.mem_bot] at this
    exact hκ1 this
  set x : GL (Fin 2) (ZMod r) := ((κ : A₂) : GL (Fin 2) (ZMod r)) with hx
  have hx10 : ent x 1 0 ≠ 0 := hκH
  have hxt : t * x * t * x = 1 := by
    have h1 := congrArg Subtype.val hσκ
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht', htinv] at h1
    rw [h1, inv_mul_cancel]
  have e1 := eq_one_iff'.mp hxt
  simp only [ent_mul, ht00, ht01, ht10, ← he] at e1
  obtain ⟨e1a, -, e1c, -⟩ := e1
  have hd : ent x 1 1 = ent x 0 0 := by
    have : (ent x 1 1 - ent x 0 0) * ent x 1 0 = 0 := by
      linear_combination e1c - ent x 1 1 * ent x 1 0 * he2 - ent x 0 0 * ent x 1 0 * ht11
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hx10
  have hxx' : x * (δ * x * δ⁻¹) = (δ * x * δ⁻¹) * x := by
    have h1 := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul, hκ'] at h1
    exact h1
  have e2 := congrArg (fun y => ent y 0 0) hxx'
  simp only [ent_mul, hδ00, hδ01, hδ10, hδ11, hδi00, hδi01, hδi10] at e2
  have hβ : ent x 0 1 = 0 := by
    have : ent x 0 1 * ent x 1 0 * (k ^ 2 - 1) = 0 := by
      linear_combination k * e2 + (ent x 0 1 * ent x 1 0) * hδi11
    rcases mul_eq_zero.mp this with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hx10
    · exact absurd (sub_eq_zero.mp h) hk2
  have hα : ent x 0 0 * ent x 0 0 = 1 := by
    rw [hβ] at e1a
    linear_combination e1a
  have hx2 : ent (x ^ 2) 0 1 = 0 ∧ ent (x ^ 2) 0 0 = 1 ∧ ent (x ^ 2) 1 1 = 1 ∧
      ent (x ^ 2) 1 0 = 2 * ent x 0 0 * ent x 1 0 := by
    rw [pow_two]
    simp only [ent_mul, hβ, hd]
    refine ⟨by ring, by linear_combination hα, by linear_combination hα, by ring⟩
  have hx2A : x ^ 2 ∈ A := A.pow_mem (hA₂A κ.2) 2
  have hx21 : x ^ 2 = 1 := by
    apply eq_one_of_pow_r hA hx2A
    obtain ⟨j00, j01, j10, j11⟩ := lower_pow hx2.1 (by rw [hx2.2.2.1, hx2.2.1]) r
    rw [hx2.2.1, one_pow] at j00 j11
    rw [hx2.2.1, mul_one, ZMod.natCast_self, zero_mul, zero_mul] at j10
    exact eq_one_iff'.mpr ⟨j00, j01, j10, j11⟩
  have h0 := (eq_one_iff'.mp hx21).2.2.1
  rw [hx2.2.2.2] at h0
  have hα0 : ent x 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hα
    exact zero_ne_one hα
  rcases mul_eq_zero.mp h0 with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact h2ne h'
    · exact hα0 h'
  · exact hx10 h

end GL2

end CFSG.Walter.W67.Sec6
