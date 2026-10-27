module

public import CFSG.Quasithin.Background.E6Nine
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.E6

open CFSG.Open CFSG.QuasithinUnique

section Center

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_center_of_oddCoreIn_eq_bot {H L : Subgroup G} (hLH : L ≤ H)
    (hLn : (L.subgroupOf H).Normal) (hO : oddCoreIn H = ⊥) :
    IsPGroup 2 ↥(Subgroup.center ↥L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup G := (Subgroup.center ↥L).map L.subtype with hZdef
  have hmemZ : ∀ z : G, z ∈ Z ↔ z ∈ L ∧ ∀ l ∈ L, l * z = z * l := by
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, fun l hl => ?_⟩
      have := Subgroup.mem_center_iff.mp hw ⟨l, hl⟩
      exact congrArg Subtype.val this
    · rintro ⟨hzL, hz⟩
      refine ⟨⟨z, hzL⟩, Subgroup.mem_center_iff.mpr fun l => Subtype.ext (hz l l.2), rfl⟩
  have hconjL : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L := by
    intro h hh l hl
    have := hLn.conj_mem ⟨l, hLH hl⟩ (Subgroup.mem_subgroupOf.mpr hl) ⟨h, hh⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hconjZ : ∀ h ∈ H, ∀ z ∈ Z, h * z * h⁻¹ ∈ Z := by
    intro h hh z hz
    obtain ⟨hzL, hzc⟩ := (hmemZ z).mp hz
    refine (hmemZ _).mpr ⟨hconjL h hh z hzL, fun l hl => ?_⟩
    have hl' : h⁻¹ * l * h ∈ L := by
      have := hconjL h⁻¹ (H.inv_mem hh) l hl
      simpa using this
    have h1 := hzc _ hl'
    calc l * (h * z * h⁻¹) = h * ((h⁻¹ * l * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * l * h)) * h⁻¹ := by rw [h1]
      _ = h * z * h⁻¹ * l := by group
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    exact ((hmemZ b).mp hb).2 a ((hmemZ a).mp ha).1
  let O : Subgroup G :=
    { carrier := {w | w ∈ Z ∧ Odd (orderOf w)}
      mul_mem' := by
        rintro a b ⟨haZ, ha⟩ ⟨hbZ, hb⟩
        refine ⟨Z.mul_mem haZ hbZ, ?_⟩
        have h1 := (Commute.orderOf_mul_dvd_lcm (hZcomm a haZ b hbZ))
        exact Odd.of_dvd_nat (ha.mul hb)
          (h1.trans (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _)))
      one_mem' := ⟨Z.one_mem, by rw [orderOf_one]; exact odd_one⟩
      inv_mem' := by
        rintro a ⟨haZ, ha⟩
        exact ⟨Z.inv_mem haZ, by rwa [orderOf_inv]⟩ }
  have hOZ : O ≤ Z := fun w hw => hw.1
  have hOH : O ≤ H := fun w hw => hLH ((hmemZ w).mp hw.1).1
  have hnorm : H ≤ Subgroup.normalizer (O : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨hwZ, hw⟩
      refine ⟨hconjZ h hh w hwZ, ?_⟩
      have e : orderOf (h * w * h⁻¹) = orderOf w := MulEquiv.orderOf_eq (MulAut.conj h) w
      rwa [e]
    · rintro ⟨hwZ, hw⟩
      have h1 := hconjZ h⁻¹ (H.inv_mem hh) _ hwZ
      have e : h⁻¹ * (h * w * h⁻¹) * h⁻¹⁻¹ = w := by group
      rw [e] at h1
      refine ⟨h1, ?_⟩
      have e' : orderOf (h * w * h⁻¹) = orderOf w := MulEquiv.orderOf_eq (MulAut.conj h) w
      rwa [e'] at hw
  have hodd : Odd (Nat.card O) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    obtain ⟨⟨w, hw⟩, hw2⟩ := exists_prime_orderOf_dvd_card' (G := O) 2 (even_iff_two_dvd.mp hev)
    have h1 : orderOf w = 2 := by rw [← Subgroup.orderOf_coe] at hw2; exact hw2
    have h2 := hw.2
    rw [h1] at h2
    exact (Nat.not_odd_iff_even.mpr even_two) h2
  have hObot : O = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact le_oddCoreIn_of_odd hOH hnorm hodd
  intro z
  have hz : ((z : ↥L) : G) ∈ Z := ⟨z, z.2, rfl⟩
  set w : G := ((z : ↥L) : G)
  obtain ⟨a, m, hm, hw⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos w).ne'
  have hwa : orderOf (w ^ 2 ^ a) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hw ▸ dvd_mul_right _ _), hw,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hmem : w ^ 2 ^ a ∈ O := ⟨Z.pow_mem hz _, hwa ▸ hm⟩
  rw [hObot, Subgroup.mem_bot] at hmem
  refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
  simpa [w] using hmem

end Center

section Lift

variable {L : Type*} [Group L]

theorem mem_zpowers_pow_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : L} (hx : x ^ p = 1)
    (j : ℕ) : x ∈ Subgroup.zpowers (x ^ 2 ^ j) := by
  have hcop : Nat.Coprime (2 ^ j) (orderOf x) := by
    refine Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx) ?_
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have h1 := Subgroup.npow_mem_zpowers (x ^ 2 ^ j) m
  rwa [hm] at h1

theorem exists_pair_of_center_two (hZ : IsPGroup 2 ↥(Subgroup.center L)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {a₀ b₀ : L ⧸ Subgroup.center L} (hab : a₀ * b₀ = b₀ * a₀) (ha : a₀ ^ p = 1)
    (hb : b₀ ^ p = 1) (ha1 : a₀ ≠ 1) (hba : b₀ ∉ Subgroup.zpowers a₀) :
    ∃ a b : L, a * b = b * a ∧ a ^ p = 1 ∧ b ^ p = 1 ∧ a ≠ 1 ∧ b ∉ Subgroup.zpowers a := by
  have hlift : ∀ c₀ : L ⧸ Subgroup.center L, c₀ ^ p = 1 →
      ∃ (c : L) (j : ℕ), (c : L ⧸ Subgroup.center L) = c₀ ^ 2 ^ j ∧ c ^ p = 1 := by
    intro c₀ hc₀
    obtain ⟨c', rfl⟩ := QuotientGroup.mk_surjective c₀
    have hcz : c' ^ p ∈ Subgroup.center L := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hc₀]
    obtain ⟨j, hj⟩ := hZ ⟨c' ^ p, hcz⟩
    refine ⟨c' ^ 2 ^ j, j, by rw [QuotientGroup.mk_pow], ?_⟩
    have := congrArg Subtype.val hj
    rw [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [← pow_mul, mul_comm, pow_mul, this]
  obtain ⟨a, j, haj, hap⟩ := hlift a₀ ha
  obtain ⟨b, j', hbj, hbp⟩ := hlift b₀ hb
  have ha₀ : a₀ ∈ Subgroup.zpowers (a₀ ^ 2 ^ j) := mem_zpowers_pow_two_pow hp hp2 ha j
  have hb₀ : b₀ ∈ Subgroup.zpowers (b₀ ^ 2 ^ j') := mem_zpowers_pow_two_pow hp hp2 hb j'
  have hz : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, haj, hbj]
    have hc : Commute (a₀ ^ 2 ^ j) (b₀ ^ 2 ^ j') := (Commute.pow_pow hab _ _)
    rw [hc.eq]
    group
  set z := a * b * a⁻¹ * b⁻¹ with hzdef
  have hzc : ∀ g : L, g * z = z * g := fun g => (Subgroup.mem_center_iff.mp hz g)
  have hconj : ∀ k : ℕ, a ^ k * b * (a ^ k)⁻¹ = z ^ k * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc a ^ (k + 1) * b * (a ^ (k + 1))⁻¹ = a * (a ^ k * b * (a ^ k)⁻¹) * a⁻¹ := by
            rw [pow_succ']; group
        _ = a * (z ^ k * b) * a⁻¹ := by rw [ih]
        _ = z ^ k * (a * b * a⁻¹) := by
            have : a * z ^ k = z ^ k * a := (Commute.pow_right (hzc a) k).eq
            calc a * (z ^ k * b) * a⁻¹ = (a * z ^ k) * b * a⁻¹ := by group
              _ = (z ^ k * a) * b * a⁻¹ := by rw [this]
              _ = z ^ k * (a * b * a⁻¹) := by group
        _ = z ^ (k + 1) * b := by rw [hzdef, pow_succ]; group
  have hzp : z ^ p = 1 := by
    have h1 := hconj p
    rw [hap, one_mul, inv_one, mul_one] at h1
    calc z ^ p = z ^ p * b * b⁻¹ := by group
      _ = b * b⁻¹ := by rw [← h1]
      _ = 1 := mul_inv_cancel b
  have hz1 : z = 1 := by
    obtain ⟨i, hi⟩ := hZ ⟨z, hz⟩
    have hi' : z ^ 2 ^ i = 1 := by
      have := congrArg Subtype.val hi
      simpa using this
    have hd1 := orderOf_dvd_of_pow_eq_one hzp
    have hd2 := orderOf_dvd_of_pow_eq_one hi'
    have hcop : Nat.Coprime p (2 ^ i) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have hcomm : a * b = b * a := by
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := hz1
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h1, one_mul]
  refine ⟨a, b, hcomm, hap, hbp, fun h1 => ?_, fun hmem => ?_⟩
  ·
    apply ha1
    have h2 : a₀ ^ 2 ^ j = 1 := by rw [← haj, h1, QuotientGroup.mk_one]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha₀
    rw [← hk, h2, one_zpow]
  ·
    apply hba
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h2 : b₀ ^ 2 ^ j' = (a₀ ^ 2 ^ j) ^ k := by
      rw [← hbj, ← haj, ← hk, QuotientGroup.mk_zpow]
    have h3 : b₀ ^ 2 ^ j' ∈ Subgroup.zpowers a₀ := by
      rw [h2]
      exact Subgroup.zpow_mem _ (Subgroup.npow_mem_zpowers _ _) k
    exact (Subgroup.zpowers_le.mpr h3) hb₀

end Lift

section PSL3

open Matrix

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
@[expose] def sl3Diag (a b c : K) (h : a * b * c = 1) : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![a, b, c], by simp [det_diagonal, Fin.prod_univ_three, h]⟩

omit [Finite K] in
theorem coe_sl3Diag (a b c : K) (h : a * b * c = 1) :
    ((sl3Diag a b c h : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![a, b, c] := rfl

omit [Finite K] in
theorem coe_sl3Diag_pow (a b c : K) (h : a * b * c = 1) (k : ℕ) :
    ((sl3Diag a b c h ^ k : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      diagonal ![a ^ k, b ^ k, c ^ k] := by
  rw [Matrix.SpecialLinearGroup.coe_pow, coe_sl3Diag, diagonal_pow]
  congr 1
  ext i
  fin_cases i <;> rfl

omit [Finite K] in
theorem exists_scalar_of_mk_eq_pow {x y : Matrix.SpecialLinearGroup (Fin 3) K} {k : ℕ}
    (h : (QuotientGroup.mk y : Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) =
      (QuotientGroup.mk x : Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) ^ k) :
    ∃ r : K, r ≠ 0 ∧ (y : Matrix (Fin 3) (Fin 3) K) =
      ((x ^ k : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        scalar (Fin 3) r := by
  rw [← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq] at h
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  refine ⟨r, fun h0 => ?_, ?_⟩
  · rw [h0, zero_pow (by simp)] at hr
    exact zero_ne_one hr
  · have e : y = x ^ k * ((x ^ k)⁻¹ * y) := by group
    rw [e, Matrix.SpecialLinearGroup.coe_mul, ← hrz]

theorem exists_pair_psl3 {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hpd : p ∣ Nat.card K - 1) :
    ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 3) K, a * b = b * a ∧ a ^ p = 1 ∧ b ^ p = 1 ∧
      a ≠ 1 ∧ b ∉ Subgroup.zpowers a := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  set l : K := (u : K) with hl
  have hl0 : l ≠ 0 := u.ne_zero
  have hlp : l ^ p = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    have h2 := congrArg (fun v : Kˣ => (v : K)) this
    simpa using h2
  have hl1 : ∀ k : ℕ, l ^ k = 1 → p ∣ k := by
    intro k hk
    have : u ^ k = 1 := Units.ext (by simpa using hk)
    rw [← hu]
    exact orderOf_dvd_of_pow_eq_one this
  let A := sl3Diag l l⁻¹ 1 (by field_simp)
  let B := sl3Diag 1 l l⁻¹ (by field_simp)
  refine ⟨QuotientGroup.mk A, QuotientGroup.mk B, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, A, B, coe_sl3Diag, diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm]
  · have hAp : A ^ p = 1 := by
      apply Subtype.ext
      rw [coe_sl3Diag_pow, Matrix.SpecialLinearGroup.coe_one, inv_pow, hlp, inv_one, one_pow]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [← QuotientGroup.mk_pow, hAp, QuotientGroup.mk_one]
  · have hBp : B ^ p = 1 := by
      apply Subtype.ext
      rw [coe_sl3Diag_pow, Matrix.SpecialLinearGroup.coe_one, inv_pow, hlp, inv_one, one_pow]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [← QuotientGroup.mk_pow, hBp, QuotientGroup.mk_one]
  · intro h1
    have h2 : (QuotientGroup.mk A : Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) =
        (QuotientGroup.mk (1 : Matrix.SpecialLinearGroup (Fin 3) K)) ^ 1 := by
      rw [h1, pow_one]
      rfl
    obtain ⟨r, -, hr⟩ := exists_scalar_of_mk_eq_pow h2
    have h00 := congrFun (congrFun hr 0) 0
    have h22 := congrFun (congrFun hr 2) 2
    simp [A, coe_sl3Diag] at h00 h22
    have : l = 1 := by rw [h00, ← h22]
    have h3 := hl1 1 (by rw [pow_one, this])
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  · intro hmem
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr hmem)
    obtain ⟨r, hr0, hr⟩ := exists_scalar_of_mk_eq_pow hk.symm
    have h00 := congrFun (congrFun hr 0) 0
    have h11 := congrFun (congrFun hr 1) 1
    have h22 := congrFun (congrFun hr 2) 2
    simp only [B, A, coe_sl3Diag, coe_sl3Diag_pow, diagonal_apply_eq, scalar_apply,
      Matrix.diagonal_mul_diagonal] at h00 h11 h22
    simp at h00 h11 h22
    rw [← h22] at h00 h11
    have e1 : l ^ k = l := by
      field_simp at h00
      exact h00.symm
    rw [e1] at h11
    have h3 : l ^ 3 = 1 := by
      field_simp at h11
      linear_combination h11
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hl1 3 h3))

omit [Finite K] in
@[expose] def sl3Cycle : Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem exists_pair_psl3_three (hpd : 3 ∣ Nat.card K - 1) :
    ∃ a b : Matrix.ProjectiveSpecialLinearGroup (Fin 3) K, a * b = b * a ∧ a ^ 3 = 1 ∧
      b ^ 3 = 1 ∧ a ≠ 1 ∧ b ∉ Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rwa [Nat.card_units])
  set w : K := (u : K) with hw
  have hw3 : w ^ 3 = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    have h2 := congrArg (fun v : Kˣ => (v : K)) this
    simpa using h2
  have hw1 : w ≠ 1 := by
    intro h
    have : u = 1 := Units.ext (by rw [Units.val_one, ← hw]; exact h)
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  let A := sl3Diag 1 w (w ^ 2) (by rw [one_mul, ← pow_succ']; exact hw3)
  let P : Matrix.SpecialLinearGroup (Fin 3) K := sl3Cycle
  let Z := sl3Diag (w ^ 2) (w ^ 2) (w ^ 2) (by rw [← pow_add, ← pow_add,
    show 2 + 2 + 2 = 3 * 2 by norm_num, pow_mul, hw3, one_pow])
  have hZ : Z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨w ^ 2, ?_, ?_⟩
    · rw [Fintype.card_fin, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hw3, one_pow]
    · simp only [Z, coe_sl3Diag]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hw4 : w ^ 4 = w := by rw [show w ^ 4 = w ^ 3 * w by ring, hw3, one_mul]
  have hPA : P * A = Z * A * P := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    simp only [P, A, Z, coe_sl3Diag, sl3Cycle]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, ← pow_succ, ← pow_add, hw3, hw4]
  refine ⟨QuotientGroup.mk A, QuotientGroup.mk P, ?_, ?_, ?_, ?_, ?_⟩
  · symm
    calc (QuotientGroup.mk P : Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) *
          QuotientGroup.mk A = QuotientGroup.mk (P * A) := rfl
      _ = QuotientGroup.mk (Z * A * P) := by rw [hPA]
      _ = QuotientGroup.mk Z * QuotientGroup.mk A * QuotientGroup.mk P := rfl
      _ = QuotientGroup.mk A * QuotientGroup.mk P := by
          rw [(QuotientGroup.eq_one_iff Z).mpr hZ, one_mul]
  · have hAp : A ^ 3 = 1 := by
      apply Subtype.ext
      rw [coe_sl3Diag_pow, Matrix.SpecialLinearGroup.coe_one, ← pow_mul,
        show 2 * 3 = 3 * 2 by norm_num, pow_mul, hw3, one_pow, one_pow]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [← QuotientGroup.mk_pow, hAp, QuotientGroup.mk_one]
  · have hPp : P ^ 3 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      simp only [P, sl3Cycle]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
    rw [← QuotientGroup.mk_pow, hPp, QuotientGroup.mk_one]
  · intro h1
    have h2 : (QuotientGroup.mk A : Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) =
        (QuotientGroup.mk (1 : Matrix.SpecialLinearGroup (Fin 3) K)) ^ 1 := by
      rw [h1, pow_one]
      rfl
    obtain ⟨r, -, hr⟩ := exists_scalar_of_mk_eq_pow h2
    have h00 := congrFun (congrFun hr 0) 0
    have h11 := congrFun (congrFun hr 1) 1
    simp [A, coe_sl3Diag] at h00 h11
    exact hw1 (by rw [h11, ← h00])
  · intro hmem
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr hmem)
    obtain ⟨r, hr0, hr⟩ := exists_scalar_of_mk_eq_pow hk.symm
    simp only [A, coe_sl3Diag_pow] at hr
    have h00 := congrFun (congrFun hr 0) 0
    simp [P, sl3Cycle] at h00
    exact hr0 h00.symm

end PSL3

section Sp4

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

@[expose] noncomputable def glDiag {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → K)
    (hd : ∀ i, d i ≠ 0) : GL ι K :=
  ⟨diagonal d, diagonal fun i => (d i)⁻¹, by
    rw [diagonal_mul_diagonal]
    convert diagonal_one (n := ι) (α := K)
    exact mul_inv_cancel₀ (hd _), by
    rw [diagonal_mul_diagonal]
    convert diagonal_one (n := ι) (α := K)
    exact inv_mul_cancel₀ (hd _)⟩

theorem coe_glDiag_pow {ι : Type} [Fintype ι] [DecidableEq ι] (d : ι → K) (hd : ∀ i, d i ≠ 0)
    (k : ℕ) : ((glDiag d hd ^ k : GL ι K) : Matrix ι ι K) = diagonal (d ^ k) := by
  rw [Units.val_pow_eq_pow_val, show ((glDiag d hd : GL ι K) : Matrix ι ι K) = diagonal d from rfl,
    diagonal_pow]

theorem mem_statedSp_glDiag {a b c e : K} (hac : a * c = 1) (hbe : b * e = 1)
    (hd : ∀ i, Sum.elim ![a, b] ![c, e] i ≠ 0) :
    glDiag (Sum.elim ![a, b] ![c, e]) hd ∈ StatedSp 2 K := by
  refine Subgroup.subset_closure ?_
  show (diagonal (Sum.elim ![a, b] ![c, e]))ᵀ * fromBlocks 0 1 (-1) 0 *
    diagonal (Sum.elim ![a, b] ![c, e]) = fromBlocks 0 1 (-1) 0
  rw [diagonal_transpose]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [fromBlocks, one_apply, hac, hbe, mul_comm c a, mul_comm e b]

theorem exists_scalar_of_mk_eq_pow_sp {x y : StatedSp 2 K} {k : ℕ}
    (h : (QuotientGroup.mk y : StatedProj (StatedSp 2 K)) =
      (QuotientGroup.mk x : StatedProj (StatedSp 2 K)) ^ k) :
    ∃ u : Kˣ, ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      (((x : GL (Fin 2 ⊕ Fin 2) K) ^ k : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) * scalar (Fin 2 ⊕ Fin 2) (u : K) := by
  rw [← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq] at h
  obtain ⟨u, hu⟩ := Subgroup.mem_subgroupOf.mp h
  refine ⟨u, ?_⟩
  have e : (y : GL (Fin 2 ⊕ Fin 2) K) =
      (x : GL (Fin 2 ⊕ Fin 2) K) ^ k * (((x ^ k)⁻¹ * y : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) := by
    simp
  rw [e, Units.val_mul, ← hu, GeneralLinearGroup.coe_scalar]

theorem exists_pair_sp4 [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ Nat.card K - 1) :
    ∃ a b : StatedProj (StatedSp 2 K), a * b = b * a ∧ a ^ p = 1 ∧ b ^ p = 1 ∧ a ≠ 1 ∧
      b ∉ Subgroup.zpowers a := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rwa [Nat.card_units])
  set l : K := (u : K) with hl
  have hl0 : l ≠ 0 := u.ne_zero
  have hlp : l ^ p = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    have h2 := congrArg (fun v : Kˣ => (v : K)) this
    simpa using h2
  have hl1 : ∀ k : ℕ, l ^ k = 1 → p ∣ k := by
    intro k hk
    have : u ^ k = 1 := Units.ext (by simpa using hk)
    rw [← hu]
    exact orderOf_dvd_of_pow_eq_one this
  have hd1 : ∀ i, Sum.elim ![l, 1] ![l⁻¹, 1] i ≠ 0 := by
    rintro (i | i) <;> fin_cases i <;> simp [hl0]
  have hd2 : ∀ i, Sum.elim ![1, l] ![1, l⁻¹] i ≠ 0 := by
    rintro (i | i) <;> fin_cases i <;> simp [hl0]
  let A : StatedSp 2 K := ⟨glDiag _ hd1, mem_statedSp_glDiag (mul_inv_cancel₀ hl0) (one_mul 1) hd1⟩
  let B : StatedSp 2 K := ⟨glDiag _ hd2, mem_statedSp_glDiag (one_mul 1) (mul_inv_cancel₀ hl0) hd2⟩
  have hApow : ∀ k : ℕ, (((A : GL (Fin 2 ⊕ Fin 2) K) ^ k : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        diagonal (Sum.elim ![l ^ k, 1] ![l⁻¹ ^ k, 1]) := by
    intro k
    rw [show (A : GL (Fin 2 ⊕ Fin 2) K) = glDiag _ hd1 from rfl, coe_glDiag_pow]
    congr 1
    ext i
    rcases i with i | i <;> fin_cases i <;> simp
  have hBpow : ∀ k : ℕ, (((B : GL (Fin 2 ⊕ Fin 2) K) ^ k : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
        diagonal (Sum.elim ![1, l ^ k] ![1, l⁻¹ ^ k]) := by
    intro k
    rw [show (B : GL (Fin 2 ⊕ Fin 2) K) = glDiag _ hd2 from rfl, coe_glDiag_pow]
    congr 1
    ext i
    rcases i with i | i <;> fin_cases i <;> simp
  refine ⟨QuotientGroup.mk A, QuotientGroup.mk B, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    show diagonal _ * diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [mul_comm]
  · have hAp : A ^ p = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, hApow, inv_pow, hlp, inv_one]
      simp only [Subgroup.coe_one, Units.val_one]
      rw [← diagonal_one]
      congr 1
      ext i
      rcases i with i | i <;> fin_cases i <;> simp
    rw [← QuotientGroup.mk_pow, hAp, QuotientGroup.mk_one]
  · have hBp : B ^ p = 1 := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, hBpow, inv_pow, hlp, inv_one]
      simp only [Subgroup.coe_one, Units.val_one]
      rw [← diagonal_one]
      congr 1
      ext i
      rcases i with i | i <;> fin_cases i <;> simp
    rw [← QuotientGroup.mk_pow, hBp, QuotientGroup.mk_one]
  · intro h1
    have h2 : (QuotientGroup.mk A : StatedProj (StatedSp 2 K)) =
        (QuotientGroup.mk (1 : StatedSp 2 K)) ^ 1 := by
      rw [h1, pow_one]
      rfl
    obtain ⟨v, hv⟩ := exists_scalar_of_mk_eq_pow_sp h2
    have e1 := congrFun (congrFun hv (Sum.inl 0)) (Sum.inl 0)
    have e2 := congrFun (congrFun hv (Sum.inl 1)) (Sum.inl 1)
    simp [A, glDiag] at e1 e2
    have : l = 1 := by rw [e1, ← e2]
    have h3 := hl1 1 (by rw [pow_one, this])
    exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
  · intro hmem
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr hmem)
    obtain ⟨v, hv⟩ := exists_scalar_of_mk_eq_pow_sp hk.symm
    rw [hApow] at hv
    have e1 := congrFun (congrFun hv (Sum.inl 0)) (Sum.inl 0)
    have e2 := congrFun (congrFun hv (Sum.inl 1)) (Sum.inl 1)
    have e3 := congrFun (congrFun hv (Sum.inr 0)) (Sum.inr 0)
    simp [B, glDiag] at e1 e2 e3
    rw [← e2] at e1 e3
    have h4 : l ^ 2 = 1 := by
      have f1 : l ^ k * l = 1 := e1.symm
      have f2 : l = l ^ k := by
        field_simp at e3
        exact e3.symm
      rw [← f2] at f1
      rw [sq]
      exact f1
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hl1 2 h4))

end Sp4

section Pair

@[expose] def IsPair {A : Type*} [Group A] (p : ℕ) (a b : A) : Prop :=
  a * b = b * a ∧ a ^ p = 1 ∧ b ^ p = 1 ∧ a ≠ 1 ∧ b ∉ Subgroup.zpowers a

theorem IsPair.map_equiv {A B : Type*} [Group A] [Group B] (φ : A ≃* B) {p : ℕ} {a b : A}
    (h : IsPair p a b) : IsPair p (φ a) (φ b) := by
  obtain ⟨hab, ha, hb, ha1, hba⟩ := h
  refine ⟨by rw [← map_mul, ← map_mul, hab], by rw [← map_pow, ha, map_one],
    by rw [← map_pow, hb, map_one], fun h1 => ha1 (φ.injective (h1.trans (map_one φ).symm)),
    fun hmem => hba ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, φ.injective ?_⟩
  rw [map_zpow, hk]

theorem exists_pair_of_lie {G : Type} [Group G] {L : Subgroup G}
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥L)) {n : ℕ}
    (hlie : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 n ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ 2 ^ n - 1) :
    ∃ a b : G, a ∈ L ∧ b ∈ L ∧ IsPair p a b := by
  have hcoe : ∀ a b : ↥L, IsPair p a b → ∃ a b : G, a ∈ L ∧ b ∈ L ∧ IsPair p a b := by
    rintro a b ⟨hab, ha, hb, ha1, hba⟩
    refine ⟨a, b, a.2, b.2, congrArg Subtype.val hab, by rw [← Subgroup.coe_pow, ha]; rfl,
      by rw [← Subgroup.coe_pow, hb]; rfl, fun h1 => ha1 (Subtype.ext h1), fun hmem => hba ?_⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow, hk])⟩
  rcases hlie with ⟨-, K, _, _, hK, ⟨e⟩⟩ | ⟨-, K, _, _, hK, ⟨e⟩⟩
  ·
    let e' := e.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm
    have hKp : p ∣ Nat.card K - 1 := by rwa [hK]
    obtain ⟨a₀, b₀, h₀⟩ : ∃ a₀ b₀ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) K,
        IsPair p a₀ b₀ := by
      by_cases hp3 : p = 3
      · subst hp3
        exact exists_pair_psl3_three hKp
      · exact exists_pair_psl3 hp hp3 hKp
    obtain ⟨hab, ha, hb, ha1, hba⟩ := h₀.map_equiv e'.symm
    obtain ⟨a, b, h⟩ := exists_pair_of_center_two hZ hp hp2 hab ha hb ha1 hba
    exact hcoe a b h
  ·
    have hKp : p ∣ Nat.card K - 1 := by rwa [hK]
    obtain ⟨a₀, b₀, h₀⟩ := exists_pair_sp4 hp hp2 hKp
    exact hcoe _ _ (IsPair.map_equiv e.symm h₀)

end Pair

end CFSG.Quasithin.E6
