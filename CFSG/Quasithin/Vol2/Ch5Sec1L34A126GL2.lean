module

public import CFSG.Quasithin.Background.A1bGL2
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.LinearCombination

public section

open Matrix

namespace CFSG.Quasithin.H13

namespace GL2Six

section Matrices

variable {F : Type*} [Field F]

theorem eq_smul_one_add_smul_of_commute {e m : Matrix (Fin 2) (Fin 2) F}
    (he : ∀ c : F, e ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) (hm : m * e = e * m) :
    ∃ x y : F, m = x • (1 : Matrix (Fin 2) (Fin 2) F) + y • e := by
  have h11 := congrFun (congrFun hm 0) 0
  have h12 := congrFun (congrFun hm 0) 1
  have h21 := congrFun (congrFun hm 1) 0
  have h22 := congrFun (congrFun hm 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h11 h12 h21 h22
  by_cases hb : e 0 1 = 0
  · by_cases hc : e 1 0 = 0
    · have had : e 0 0 - e 1 1 ≠ 0 := by
        intro h
        apply he (e 0 0)
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hb, hc]
        linear_combination -h
      have hq : m 0 1 = 0 := by
        rw [hb] at h12
        have : m 0 1 * (e 0 0 - e 1 1) = 0 := by linear_combination -h12
        exact (mul_eq_zero.mp this).resolve_right had
      have hr : m 1 0 = 0 := by
        rw [hc] at h21
        have : m 1 0 * (e 0 0 - e 1 1) = 0 := by linear_combination h21
        exact (mul_eq_zero.mp this).resolve_right had
      refine ⟨m 0 0 - (m 0 0 - m 1 1) / (e 0 0 - e 1 1) * e 0 0,
        (m 0 0 - m 1 1) / (e 0 0 - e 1 1), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hc, hq, hr]
      field_simp
      ring
    · refine ⟨m 1 1 - m 1 0 / e 1 0 * e 1 1, m 1 0 / e 1 0, ?_⟩
      have hq : m 0 1 = 0 := by
        rw [hb] at h22
        have : e 1 0 * m 0 1 = 0 := by linear_combination -h22
        exact (mul_eq_zero.mp this).resolve_left hc
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb, hq]
      · field_simp
        linear_combination -h21
      · field_simp
  · refine ⟨m 0 0 - m 0 1 / e 0 1 * e 0 0, m 0 1 / e 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · field_simp
    · field_simp
      linear_combination -h11
    · field_simp
      linear_combination -h12

theorem trace_smul_one_add_smul (x y : F) (e : Matrix (Fin 2) (Fin 2) F) :
    (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • e).trace = 2 * x + y * e.trace := by
  simp [Matrix.trace_fin_two]
  ring

theorem det_smul_one_add_smul (x y : F) (e : Matrix (Fin 2) (Fin 2) F) :
    (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • e).det =
      x ^ 2 + x * y * e.trace + y ^ 2 * e.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

theorem disc_ne_zero (h2 : (2 : F) ≠ 0) {e : Matrix (Fin 2) (Fin 2) F}
    (he : ∀ c : F, e ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) {k : ℕ} (hk : e ^ (2 ^ k) = 1) :
    e.trace ^ 2 - 4 * e.det ≠ 0 := by
  intro hd
  set l : F := e.trace / 2 with hl
  set N : Matrix (Fin 2) (Fin 2) F := e - l • (1 : Matrix (Fin 2) (Fin 2) F) with hN
  have hCH := A1b.GL2.cayley_hamilton_two e
  have h2l : e.trace = 2 * l := by rw [hl]; field_simp
  have hdet : e.det = l ^ 2 := by
    have h4 : (4 : F) ≠ 0 := by
      have : (4 : F) = 2 * 2 := by norm_num
      rw [this]
      exact mul_ne_zero h2 h2
    have : 4 * e.det = 4 * l ^ 2 := by rw [h2l] at hd; linear_combination -hd
    exact mul_left_cancel₀ h4 this
  have he' : e = l • (1 : Matrix (Fin 2) (Fin 2) F) + N := by rw [hN]; abel
  have hNN : N * N = 0 := by
    have h1 : N * N = e * e - (2 * l) • e + (l ^ 2) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [hN, sub_mul, mul_sub, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
        smul_mul_assoc, one_mul, smul_smul]
      rw [two_mul, add_smul, sq]
      abel
    rw [h1, hCH, h2l, hdet]
    abel
  have hN0 : N ≠ 0 := by
    intro h
    apply he l
    rw [he', h, add_zero]
  have hdet0 : e.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hk
    rw [Matrix.det_pow, h0, Matrix.det_one, zero_pow (pow_ne_zero _ two_ne_zero)] at this
    exact zero_ne_one this
  have hl0 : l ≠ 0 := by
    intro h0
    apply hdet0
    rw [hdet, h0]
    ring
  have key : ∀ j : ℕ, ∃ α β : F, α ≠ 0 ∧ β ≠ 0 ∧
      e ^ (2 ^ j) = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • N := by
    intro j
    induction j with
    | zero => exact ⟨l, 1, hl0, one_ne_zero, by rw [pow_zero, pow_one, one_smul]; exact he'⟩
    | succ j ih =>
      obtain ⟨α, β, hα, hβ, h⟩ := ih
      refine ⟨α ^ 2, 2 * α * β, pow_ne_zero 2 hα, mul_ne_zero (mul_ne_zero h2 hα) hβ, ?_⟩
      rw [pow_succ, pow_mul, h, sq]
      rw [add_mul, mul_add, mul_add, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul,
        mul_smul_comm, mul_one, smul_mul_assoc, mul_smul_comm, hNN, smul_zero, smul_zero,
        add_zero, smul_smul, smul_smul]
      rw [sq, show 2 * α * β = α * β + α * β by ring, add_smul]
      abel
  obtain ⟨α, β, -, hβ, h⟩ := key k
  rw [hk] at h
  have hN' : N = ((1 - α) / β) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h3 : β • N = (1 - α) • (1 : Matrix (Fin 2) (Fin 2) F) := by
      rw [sub_smul, one_smul]
      exact eq_sub_of_add_eq' h.symm
    calc N = β⁻¹ • (β • N) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
      _ = ((1 - α) / β) • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [h3, smul_smul, div_eq_inv_mul]
  have h5 : ((1 - α) / β) ^ 2 = 0 := by
    have := congrFun (congrFun hNN 0) 0
    rw [hN'] at this
    simpa [Matrix.mul_apply, Fin.sum_univ_two, sq] using this
  apply hN0
  rw [hN', pow_eq_zero_iff two_ne_zero |>.mp h5, zero_smul]

theorem eq_or_eq_trace_sub_of_commute (h2 : (2 : F) ≠ 0) {e h : Matrix (Fin 2) (Fin 2) F}
    (he : ∀ c : F, e ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) {k : ℕ} (hk : e ^ (2 ^ k) = 1)
    (hc : h * e = e * h) (ht : h.trace = e.trace) (hd : h.det = e.det) :
    h = e ∨ h = e.trace • (1 : Matrix (Fin 2) (Fin 2) F) - e := by
  obtain ⟨x, y, rfl⟩ := eq_smul_one_add_smul_of_commute he hc
  rw [trace_smul_one_add_smul] at ht
  rw [det_smul_one_add_smul] at hd
  have hdisc := disc_ne_zero h2 he hk
  have key : (1 - y ^ 2) * (e.trace ^ 2 - 4 * e.det) = 0 := by
    linear_combination 4 * hd - (2 * x + y * e.trace + e.trace) * ht
  have hy : y ^ 2 = 1 := by
    have := (mul_eq_zero.mp key).resolve_right hdisc
    linear_combination -this
  have hy' : y * y = 1 := by rw [← sq]; exact hy
  rcases mul_self_eq_one_iff.mp hy' with hy1 | hy1
  · left
    have hx : x = 0 := by
      have : 2 * x = 0 := by rw [hy1] at ht; linear_combination ht
      exact (mul_eq_zero.mp this).resolve_left h2
    rw [hx, hy1, zero_smul, zero_add, one_smul]
  · right
    have hx : x = e.trace := by
      have : 2 * (x - e.trace) = 0 := by rw [hy1] at ht; linear_combination ht
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h2)
    rw [hx, hy1, neg_one_smul, sub_eq_add_neg]

end Matrices

section Coprime

variable {G : Type*} [Group G]

theorem commute_of_odd_of_sq {g a : G} (hodd : Odd (orderOf g)) (h : g * g * a = a * (g * g)) :
    g * a = a * g := by
  obtain ⟨k, hk⟩ := hodd
  have hgk : g = (g * g) ^ (k + 1) := by
    have h5 : g ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
    calc g = g ^ (2 * k + 1) * g := by rw [h5, one_mul]
      _ = g ^ (2 * k + 2) := by rw [← pow_succ]
      _ = (g * g) ^ (k + 1) := by rw [← sq, ← pow_mul]; ring_nf
  have h6 : Commute g a := by
    rw [hgk]
    exact Commute.pow_left h (k + 1)
  exact h6.eq

theorem commute_of_mem_of_commute {N : Subgroup G} (hN2 : IsPGroup 2 N) {g a : G}
    (hgN : ∀ u ∈ N, g * u = u * g) (hodd : Odd (orderOf g))
    (hu : a⁻¹ * (g * a * g⁻¹) ∈ N) : g * a = a * g := by
  set u := a⁻¹ * (g * a * g⁻¹) with hudef
  have hgu : ∀ j : ℕ, g * u ^ j = u ^ j * g := fun j => by
    have h := hgN u hu
    exact (Commute.pow_right h j).eq
  have hpow : ∀ j : ℕ, g ^ j * a * (g ^ j)⁻¹ = a * u ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e1 : g * a * g⁻¹ = a * u := by rw [hudef]; group
      calc g ^ (j + 1) * a * (g ^ (j + 1))⁻¹ = g * (g ^ j * a * (g ^ j)⁻¹) * g⁻¹ := by group
        _ = g * (a * u ^ j) * g⁻¹ := by rw [ih]
        _ = (g * a * g⁻¹) * (g * u ^ j * g⁻¹) := by group
        _ = (a * u) * u ^ j := by rw [e1, hgu j]; group
        _ = a * u ^ (j + 1) := by rw [pow_succ']; group
  have hm := hpow (orderOf g)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hm
  have hum : u ^ orderOf g = 1 := by
    have := congrArg (a⁻¹ * ·) hm
    simpa using this.symm
  obtain ⟨k, hk⟩ := hN2 ⟨u, hu⟩
  have hk' : u ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hcop : Nat.Coprime (orderOf g) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  have hu1 : u = 1 := by
    have := pow_gcd_eq_one.2 ⟨hum, hk'⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have e1 : g * a * g⁻¹ = a := by
    have := congrArg (a * ·) hu1
    simp only [hudef, mul_inv_cancel_left, mul_one] at this
    exact this
  calc g * a = g * a * g⁻¹ * g := by group
    _ = a * g := by rw [e1]

theorem index_subgroupOf_eq_two {A D : Subgroup G}
    (hD : ∀ a ∈ A, ∀ b ∈ A, a ∉ D → b ∉ D → b⁻¹ * a ∈ D) {x : G} (hxA : x ∈ A) (hxD : x ∉ D) :
    (D.subgroupOf A).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x, hxA⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hb : (b : G) ∈ D
  · exact Or.inr ⟨hb, fun h => hxD (by simpa using D.mul_mem (D.inv_mem hb) h)⟩
  · refine Or.inl ⟨?_, hb⟩
    have := hD x hxA (b⁻¹ : G) (A.inv_mem b.2) hxD (fun h => hb (by simpa using D.inv_mem h))
    simpa using this

theorem inv_mul_conj_mem_center {A : Subgroup G} [Finite A] {g : G}
    (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hcop : Nat.Coprime (orderOf g) 6) (hg0 : 0 < orderOf g)
    (hidx : (Subgroup.center ↥A).index ≤ 4) (a : ↥A) :
    a⁻¹ * ⟨g * a * g⁻¹, hg a a.2⟩ ∈ Subgroup.center ↥A := by
  classical
  set m := orderOf g with hm
  have hgm : g ^ m = 1 := pow_orderOf_eq_one g
  have hgpow : ∀ j : ℕ, ∀ x ∈ A, g ^ j * x * (g ^ j)⁻¹ ∈ A := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      have := hg _ (ih x hx)
      rw [pow_succ']
      convert this using 1
      group
  have hginv : ∀ x ∈ A, g⁻¹ * x * g ∈ A := by
    intro x hx
    have h1 : g ^ (m - 1) = g⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hg0, hgm]
    have := hgpow (m - 1) x hx
    rwa [h1, inv_inv] at this
  let ψ : ↥A →* ↥A :=
    { toFun := fun x => ⟨g * x * g⁻¹, hg x x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp only [Subgroup.coe_mul]; group }
  have hψ : ∀ x : ↥A, ((ψ x : ↥A) : G) = g * x * g⁻¹ := fun x => rfl
  have hψc : Subgroup.center ↥A ≤ (Subgroup.center ↥A).comap ψ := by
    intro z hz
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y
    set y' : ↥A := ⟨g⁻¹ * y * g, hginv y y.2⟩
    have hy : ψ y' = y := by ext; rw [hψ]; simp only [y']; group
    rw [← hy, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y']
  set φ := QuotientGroup.map (Subgroup.center ↥A) (Subgroup.center ↥A) ψ hψc with hφ
  have hiter : ∀ (j : ℕ) (x : ↥A), (⇑φ)^[j] (x : ↥A ⧸ Subgroup.center ↥A) =
      ((⟨g ^ j * x * (g ^ j)⁻¹, hgpow j x x.2⟩ : ↥A) : ↥A ⧸ Subgroup.center ↥A) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', ih, hφ, QuotientGroup.map_mk]
      congr 1
      ext
      rw [hψ]
      simp only [pow_succ']
      group
  have hφm : ∀ q : ↥A ⧸ Subgroup.center ↥A, (⇑φ)^[m] q = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [hiter]
      congr 1
      ext
      simp [hgm]
  have hm1 : m = (m - 1) + 1 := (Nat.sub_add_cancel hg0).symm
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 := congrArg (⇑φ)^[m - 1] hxy
    rw [← Function.iterate_succ_apply, ← Function.iterate_succ_apply, Nat.succ_eq_add_one,
      ← hm1, hφm, hφm] at h1
    exact h1
  have hsurj : Function.Surjective φ := by
    intro q
    refine ⟨(⇑φ)^[m - 1] q, ?_⟩
    rw [← Function.iterate_succ_apply' (⇑φ), Nat.succ_eq_add_one, ← hm1, hφm]
  let σ : Equiv.Perm (↥A ⧸ Subgroup.center ↥A) := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  have hσm : σ ^ m = 1 := by
    ext q
    rw [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id]
    exact hφm q
  have hσ1 : σ = 1 := by
    have h1 : orderOf σ ∣ m := orderOf_dvd_of_pow_eq_one hσm
    have h2 : orderOf σ ∣ 24 := by
      have h3 := orderOf_dvd_natCard σ
      rw [Nat.card_perm] at h3
      have h4 : (Nat.card (↥A ⧸ Subgroup.center ↥A)).factorial ∣ (4 : ℕ).factorial :=
        Nat.factorial_dvd_factorial hidx
      exact h3.trans h4
    have hcop24 : Nat.Coprime m 24 := by
      have h2' : Nat.Coprime m 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
      have h3' : Nat.Coprime m 3 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
      have : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [this]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 3 h2') h3'
    have := Nat.eq_one_of_dvd_coprimes hcop24 h1 h2
    exact orderOf_eq_one_iff.mp this
  have hfix : φ (a : ↥A ⧸ Subgroup.center ↥A) = (a : ↥A ⧸ Subgroup.center ↥A) := by
    have := congrArg (fun τ : Equiv.Perm (↥A ⧸ Subgroup.center ↥A) =>
      τ (a : ↥A ⧸ Subgroup.center ↥A)) hσ1
    exact this
  rw [hφ, QuotientGroup.map_mk] at hfix
  have := QuotientGroup.eq.mp hfix.symm
  exact this

end Coprime

section Group

variable {F : Type*} [Field F]

theorem conj_val_eq_or (h2 : (2 : F) ≠ 0) {e g : GL (Fin 2) F}
    (he : ∀ c : F, (e : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    {k : ℕ} (hk : e ^ (2 ^ k) = 1) (hc : g * e * g⁻¹ * e = e * (g * e * g⁻¹)) :
    ((g * e * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (e : Matrix (Fin 2) (Fin 2) F) ∨
      ((g * e * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (e : Matrix (Fin 2) (Fin 2) F).trace • (1 : Matrix (Fin 2) (Fin 2) F) -
          (e : Matrix (Fin 2) (Fin 2) F) := by
  have hcoe : ((g * e * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (g : Matrix (Fin 2) (Fin 2) F) * (e : Matrix (Fin 2) (Fin 2) F) *
        ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by simp
  have hgg' : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have ht : ((g * e * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace =
      (e : Matrix (Fin 2) (Fin 2) F).trace := by
    rw [hcoe, Matrix.trace_mul_cycle, hgg', one_mul]
  have hd : ((g * e * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      (e : Matrix (Fin 2) (Fin 2) F).det := by
    rw [hcoe, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hgg',
      Matrix.det_one, one_mul]
  have hk' : (e : Matrix (Fin 2) (Fin 2) F) ^ (2 ^ k) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hk, Units.val_one]
  have hc' : ((g * e * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (e : Matrix (Fin 2) (Fin 2) F) = (e : Matrix (Fin 2) (Fin 2) F) *
        ((g * e * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Units.val_mul, ← Units.val_mul, hc]
  exact eq_or_eq_trace_sub_of_commute h2 he hk' hc' ht hd

theorem sq_commute_of_conj_commute (h2 : (2 : F) ≠ 0) {e g : GL (Fin 2) F}
    (he : ∀ c : F, (e : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    {k : ℕ} (hk : e ^ (2 ^ k) = 1) (hc : g * e * g⁻¹ * e = e * (g * e * g⁻¹)) :
    g * g * e = e * (g * g) := by
  have h3 : g * (g * e * g⁻¹) * g⁻¹ = e := by
    rcases conj_val_eq_or h2 he hk hc with h1 | h1
    · have : g * e * g⁻¹ = e := Units.ext h1
      rw [this, this]
    · apply Units.ext
      have hgg : (g : Matrix (Fin 2) (Fin 2) F) * ((g⁻¹ : GL (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have hcoe : ((g * (g * e * g⁻¹) * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          (g : Matrix (Fin 2) (Fin 2) F) *
            ((g * e * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by simp
      have hcoe' : ((g * e * g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          (g : Matrix (Fin 2) (Fin 2) F) * (e : Matrix (Fin 2) (Fin 2) F) *
            ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by simp
      rw [hcoe, h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hgg, ← hcoe', h1]
      abel
  calc g * g * e = (g * (g * e * g⁻¹) * g⁻¹) * (g * g) := by group
    _ = e * (g * g) := by rw [h3]

theorem exists_nonscalar_of_not_comm {A : Subgroup (GL (Fin 2) F)} [Finite A]
    (hA2 : IsPGroup 2 A) (hna : ¬ ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∃ n ∈ A, (∀ c : F, (n : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) ∧
      ∀ a ∈ A, a * n * a⁻¹ * n = n * (a * n * a⁻¹) := by
  have hZ : Subgroup.center ↥A ≠ ⊤ := by
    intro h
    apply hna
    intro a ha b hb
    have := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top (⟨a, ha⟩ : ↥A)) ⟨b, hb⟩
    exact (congrArg Subtype.val this).symm
  have : Nontrivial (↥A ⧸ Subgroup.center ↥A) := QuotientGroup.nontrivial_iff.mpr hZ
  have hQ2 : IsPGroup 2 (↥A ⧸ Subgroup.center ↥A) := hA2.to_quotient _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hQ2.center_nontrivial
  obtain ⟨q, hq⟩ := exists_ne (1 : Subgroup.center (↥A ⧸ Subgroup.center ↥A))
  obtain ⟨n₀, hn₀⟩ := QuotientGroup.mk_surjective (q : ↥A ⧸ Subgroup.center ↥A)
  refine ⟨n₀, n₀.2, fun c hc => ?_, fun a ha => ?_⟩
  · apply hq
    apply Subtype.ext
    rw [← hn₀, Subgroup.coe_one, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  ·
    set a₀ : ↥A := ⟨a, ha⟩
    have hz : a₀ * n₀ * a₀⁻¹ * n₀⁻¹ ∈ Subgroup.center ↥A := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hn₀]
      have hc := Subgroup.mem_center_iff.mp q.2 (a₀ : ↥A ⧸ Subgroup.center ↥A)
      rw [hc]
      group
    set z : ↥A := a₀ * n₀ * a₀⁻¹ * n₀⁻¹ with hzdef
    have hzc : n₀ * z = z * n₀ := Subgroup.mem_center_iff.mp hz n₀
    have e : a₀ * n₀ * a₀⁻¹ = z * n₀ := by rw [hzdef]; group
    have key : a₀ * n₀ * a₀⁻¹ * n₀ = n₀ * (a₀ * n₀ * a₀⁻¹) := by
      calc a₀ * n₀ * a₀⁻¹ * n₀ = (z * n₀) * n₀ := by rw [e]
        _ = (n₀ * z) * n₀ := by rw [hzc]
        _ = n₀ * (z * n₀) := by group
        _ = n₀ * (a₀ * n₀ * a₀⁻¹) := by rw [e]
    have := congrArg Subtype.val key
    simpa using this

theorem commute_of_commute_nonscalar {n x y : GL (Fin 2) F}
    (hn : ∀ c : F, (n : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    (hx : x * n = n * x) (hy : y * n = n * y) : x * y = y * x := by
  have hx' : (x : Matrix (Fin 2) (Fin 2) F) * n = n * x := by
    rw [← Units.val_mul, ← Units.val_mul, hx]
  have hy' : (y : Matrix (Fin 2) (Fin 2) F) * n = n * y := by
    rw [← Units.val_mul, ← Units.val_mul, hy]
  obtain ⟨x₁, x₂, hxm⟩ := eq_smul_one_add_smul_of_commute hn hx'
  obtain ⟨y₁, y₂, hym⟩ := eq_smul_one_add_smul_of_commute hn hy'
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hxm, hym]
  have h1 : Commute ((1 : Matrix (Fin 2) (Fin 2) F)) (n : Matrix (Fin 2) (Fin 2) F) :=
    Commute.one_left _
  have hc : Commute (x₁ • (1 : Matrix (Fin 2) (Fin 2) F) + x₂ • (n : Matrix (Fin 2) (Fin 2) F))
      (y₁ • (1 : Matrix (Fin 2) (Fin 2) F) + y₂ • (n : Matrix (Fin 2) (Fin 2) F)) := by
    refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
    · exact ((Commute.one_left _).smul_left x₁).smul_right y₁
    · exact (h1.smul_left x₁).smul_right y₂
    · exact (h1.symm.smul_left x₂).smul_right y₁
    · exact ((Commute.refl _).smul_left x₂).smul_right y₂
  exact hc.eq

theorem inv_mul_commute_of_not_commute (h2 : (2 : F) ≠ 0) {n : GL (Fin 2) F}
    (hn : ∀ c : F, (n : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F))
    {k : ℕ} (hk : n ^ (2 ^ k) = 1) {a b : GL (Fin 2) F}
    (ha : a * n * a⁻¹ * n = n * (a * n * a⁻¹)) (hb : b * n * b⁻¹ * n = n * (b * n * b⁻¹))
    (han : ¬ a * n = n * a) (hbn : ¬ b * n = n * b) : b⁻¹ * a * n = n * (b⁻¹ * a) := by
  have hne : ∀ x : GL (Fin 2) F, ¬ x * n = n * x →
      ((x * n * x⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) ≠
        (n : Matrix (Fin 2) (Fin 2) F) := by
    intro x hx h
    apply hx
    have h' : x * n * x⁻¹ = n := Units.ext h
    calc x * n = x * n * x⁻¹ * x := by group
      _ = n * x := by rw [h']
  have hea := (conj_val_eq_or h2 hn hk ha).resolve_left (hne a han)
  have heb := (conj_val_eq_or h2 hn hk hb).resolve_left (hne b hbn)
  have hab : a * n * a⁻¹ = b * n * b⁻¹ := Units.ext (hea.trans heb.symm)
  calc b⁻¹ * a * n = b⁻¹ * (a * n * a⁻¹) * a := by group
    _ = b⁻¹ * (b * n * b⁻¹) * a := by rw [hab]
    _ = n * (b⁻¹ * a) := by group

theorem commute_of_normalizes_of_coprime_six [Finite F] (h2 : (2 : F) ≠ 0)
    {A : Subgroup (GL (Fin 2) F)} (hA2 : IsPGroup 2 A) {g : GL (Fin 2) F}
    (hg : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hcop : Nat.Coprime (orderOf g) 6) {a : GL (Fin 2) F}
    (ha : a ∈ A) : g * a = a * g := by
  classical
  have hm0 : 0 < orderOf g := orderOf_pos g
  have hodd : Odd (orderOf g) :=
    Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right (by norm_num) hcop)
  have hord : ∀ x ∈ A, ∃ k : ℕ, x ^ (2 ^ k) = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hA2 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hscalar : ∀ x y : GL (Fin 2) F, ∀ c : F,
      (x : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F) → y * x = x * y := by
    intro x y c hc
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul]
  have hstep : ∀ e ∈ A, g * e * g⁻¹ * e = e * (g * e * g⁻¹) → g * e = e * g := by
    intro e he hc
    by_cases hs : ∃ c : F, (e : Matrix (Fin 2) (Fin 2) F) = c • (1 : Matrix (Fin 2) (Fin 2) F)
    · obtain ⟨c, hc'⟩ := hs
      exact hscalar e g c hc'
    · push Not at hs
      obtain ⟨k, hk⟩ := hord e he
      exact commute_of_odd_of_sq hodd (sq_commute_of_conj_commute h2 hs hk hc)
  by_cases hidx : (Subgroup.center ↥A).index ≤ 4
  ·
    have hz := inv_mul_conj_mem_center hg hcop hm0 hidx ⟨a, ha⟩
    set z : ↥A := (⟨a, ha⟩ : ↥A)⁻¹ * ⟨g * a * g⁻¹, hg a ha⟩ with hzdef
    have hza : ((⟨a, ha⟩ : ↥A) * z : ↥A) = ⟨g * a * g⁻¹, hg a ha⟩ := by
      rw [hzdef, mul_inv_cancel_left]
    have hzc : (z : GL (Fin 2) F) * a = a * z :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨a, ha⟩).symm
    have hval : g * a * g⁻¹ = a * z := (congrArg Subtype.val hza).symm
    refine hstep a ha ?_
    rw [hval, mul_assoc, hzc]
  ·
    have hna : ¬ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
      intro hab
      apply hidx
      have : Subgroup.center ↥A = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (hab y y.2 x x.2)
      rw [this, Subgroup.index_top]
      norm_num
    obtain ⟨n, hnA, hns, hnc⟩ := exists_nonscalar_of_not_comm hA2 hna
    obtain ⟨k, hk⟩ := hord n hnA
    have hgpow : ∀ j : ℕ, ∀ x ∈ A, g ^ j * x * (g ^ j)⁻¹ ∈ A := by
      intro j
      induction j with
      | zero => intro x hx; simpa using hx
      | succ j ih =>
        intro x hx
        have := hg _ (ih x hx)
        rw [pow_succ']
        convert this using 1
        group
    have hginv : ∀ x ∈ A, g⁻¹ * x * g ∈ A := by
      intro x hx
      have h1 : g ^ (orderOf g - 1) = g⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hm0, pow_orderOf_eq_one]
      have := hgpow (orderOf g - 1) x hx
      rwa [h1, inv_inv] at this
    have hcomm : g * n * g⁻¹ * n = n * (g * n * g⁻¹) := by
      by_contra hnot
      set n₁ := g * n * g⁻¹ with hn₁
      have hn₁A : n₁ ∈ A := hg n hnA
      have hn₁s : ∀ c : F, (n₁ : Matrix (Fin 2) (Fin 2) F) ≠
          c • (1 : Matrix (Fin 2) (Fin 2) F) := by
        intro c hc
        apply hns c
        have e : n = g⁻¹ * n₁ * g := by rw [hn₁]; group
        rw [e, Units.val_mul, Units.val_mul, hc, Matrix.mul_smul, Matrix.mul_one,
          Matrix.smul_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      have hk₁ : n₁ ^ (2 ^ k) = 1 := by rw [hn₁, conj_pow, hk]; group
      have hn₁c : ∀ x ∈ A, x * n₁ * x⁻¹ * n₁ = n₁ * (x * n₁ * x⁻¹) := by
        intro x hx
        have h1 := hnc (g⁻¹ * x * g) (hginv x hx)
        have h2 := congrArg (fun y => g * y * g⁻¹) h1
        rw [hn₁]
        convert h2 using 1 <;> group
      have hidx2 : ∀ e : GL (Fin 2) F, e ∈ A →
          (∀ c : F, (e : Matrix (Fin 2) (Fin 2) F) ≠ c • (1 : Matrix (Fin 2) (Fin 2) F)) →
          e ^ (2 ^ k) = 1 → (∀ x ∈ A, x * e * x⁻¹ * e = e * (x * e * x⁻¹)) →
          ((A ⊓ Subgroup.centralizer {e}).subgroupOf A).index ≤ 2 := by
        intro e heA hes hek hec
        by_cases hall : ∀ x ∈ A, x ∈ A ⊓ Subgroup.centralizer {e}
        · have : (A ⊓ Subgroup.centralizer {e}).subgroupOf A = ⊤ := by
            rw [eq_top_iff]
            intro x _
            exact Subgroup.mem_subgroupOf.mpr (hall x x.2)
          rw [this, Subgroup.index_top]
          norm_num
        · push Not at hall
          obtain ⟨x, hxA, hxD⟩ := hall
          have hmem : ∀ y ∈ A, y ∈ A ⊓ Subgroup.centralizer {e} ↔ y * e = e * y := by
            intro y hy
            rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
            exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
          refine (index_subgroupOf_eq_two (fun a' ha' b hb ha'D hbD => ?_) hxA hxD).le
          rw [hmem _ (A.mul_mem (A.inv_mem hb) ha')]
          exact inv_mul_commute_of_not_commute h2 hes hek (hec a' ha') (hec b hb)
            (fun h => ha'D ((hmem a' ha').mpr h)) (fun h => hbD ((hmem b hb).mpr h))
      have h1 := hidx2 n hnA hns hk hnc
      have h2' := hidx2 n₁ hn₁A hn₁s hk₁ hn₁c
      have hle : (A ⊓ Subgroup.centralizer {n}).subgroupOf A ⊓
          (A ⊓ Subgroup.centralizer {n₁}).subgroupOf A ≤ Subgroup.center ↥A := by
        intro y hy
        rw [Subgroup.mem_inf] at hy
        obtain ⟨hy1, hy2⟩ := hy
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
          at hy1 hy2
        by_cases hs : ∃ c : F, ((y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
            c • (1 : Matrix (Fin 2) (Fin 2) F)
        · obtain ⟨c, hc⟩ := hs
          rw [Subgroup.mem_center_iff]
          intro w
          exact Subtype.ext (hscalar (y : GL (Fin 2) F) w c hc)
        · push Not at hs
          exact absurd (commute_of_commute_nonscalar hs hy1.2.symm hy2.2.symm).symm hnot
      have h3 := Subgroup.index_inf_le (H := (A ⊓ Subgroup.centralizer {n}).subgroupOf A)
        (K := (A ⊓ Subgroup.centralizer {n₁}).subgroupOf A)
      have h4 : (Subgroup.center ↥A).index ≤
          ((A ⊓ Subgroup.centralizer {n}).subgroupOf A ⊓
            (A ⊓ Subgroup.centralizer {n₁}).subgroupOf A).index :=
        Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le hle)
      have : (Subgroup.center ↥A).index ≤ 4 := by
        calc (Subgroup.center ↥A).index ≤ _ := h4
          _ ≤ _ := h3
          _ ≤ 2 * 2 := Nat.mul_le_mul h1 h2'
          _ = 4 := by norm_num
      exact hidx this
    have hgn : g * n = n * g := hstep n hnA hcomm
    have hy : a⁻¹ * g * a * n = n * (a⁻¹ * g * a) := by
      have hc := hnc a⁻¹ (A.inv_mem ha)
      rw [inv_inv] at hc
      have hya : (a⁻¹ * g * a) * (a⁻¹ * n * a) = (a⁻¹ * n * a) * (a⁻¹ * g * a) := by
        calc (a⁻¹ * g * a) * (a⁻¹ * n * a) = a⁻¹ * (g * n) * a := by group
          _ = a⁻¹ * (n * g) * a := by rw [hgn]
          _ = (a⁻¹ * n * a) * (a⁻¹ * g * a) := by group
      have hcv : ((a⁻¹ * n * a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
          (n : Matrix (Fin 2) (Fin 2) F) ∨
          ((a⁻¹ * n * a : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
            (n : Matrix (Fin 2) (Fin 2) F).trace • (1 : Matrix (Fin 2) (Fin 2) F) -
              (n : Matrix (Fin 2) (Fin 2) F) := by
        have := conj_val_eq_or h2 hns hk (g := a⁻¹) (by rw [inv_inv]; exact hc)
        rwa [inv_inv] at this
      apply Units.ext
      have hya' := congrArg (fun y : GL (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F)) hya
      simp only [Units.val_mul] at hya' ⊢
      rcases hcv with h | h
      · simp only [Units.val_mul] at h
        rw [h] at hya'
        simpa only [mul_assoc] using hya'
      · simp only [Units.val_mul] at h
        rw [h, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
          Matrix.one_mul] at hya'
        have := sub_right_injective hya'
        simpa only [mul_assoc] using this
    have hyg : (a⁻¹ * g * a) * g = g * (a⁻¹ * g * a) :=
      commute_of_commute_nonscalar hns hy hgn
    have hu : a⁻¹ * (g * a * g⁻¹) ∈ A ⊓ Subgroup.centralizer {g} := by
      refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem ha) (hg a ha), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine Eq.symm ?_
      calc g * (a⁻¹ * (g * a * g⁻¹)) = g * (a⁻¹ * g * a) * g⁻¹ := by group
        _ = (a⁻¹ * g * a) * g * g⁻¹ := by rw [← hyg]
        _ = a⁻¹ * (g * a * g⁻¹) * g := by group
    refine commute_of_mem_of_commute (hA2.to_le inf_le_left) (fun u hu' => ?_) hodd hu
    have := Subgroup.mem_centralizer_singleton_iff.mp hu'.2
    exact this.symm

end Group

end GL2Six

end CFSG.Quasithin.H13
