module

public import CFSG.Quasithin.Background.A1bPGroups
import CFSG.SignalizerFunctorTheorem.Quadratic.SL2

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open Matrix CFSG.SignalizerFunctorTheorem.Quadratic

section Matrices

variable {F : Type*} [Field F]

private theorem mul_self_fin_two (m : Matrix (Fin 2) (Fin 2) F) :
    m * m = m.trace • m - m.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two] <;> ring

private theorem det_eq_zero_of_mul_self_eq_zero {m : Matrix (Fin 2) (Fin 2) F} (h : m * m = 0) :
    m.det = 0 := by
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_zero] at this
  exact mul_self_eq_zero.mp this

private theorem trace_eq_zero_of_mul_self_eq_zero {m : Matrix (Fin 2) (Fin 2) F}
    (h : m * m = 0) : m.trace = 0 := by
  by_contra ht
  have h1 := mul_self_fin_two m
  rw [h, det_eq_zero_of_mul_self_eq_zero h, zero_smul, sub_zero] at h1
  have hm : m = 0 := by
    have := congrArg (fun z => m.trace⁻¹ • z) h1
    simpa [smul_smul, inv_mul_cancel₀ ht] using this.symm
  apply ht
  rw [hm, Matrix.trace_zero]

private theorem entries_eq_zero_of_trace {a b c d e f g h : F} (hA1 : a + d = 0)
    (hA2 : a * d - b * c = 0) (hB1 : e + h = 0) (hB2 : e * h - f * g = 0)
    (ht : a * e + b * g + c * f + d * h = 0) :
    a * e + b * g = 0 ∧ a * f + b * h = 0 ∧ c * e + d * g = 0 ∧ c * f + d * h = 0 := by
  obtain rfl : d = -a := by linear_combination hA1
  obtain rfl : h = -e := by linear_combination hB1
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ?_
    linear_combination (b * g) * ht - e ^ 2 * hA2 + (b * c) * hB2
  · refine pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ?_
    linear_combination (-(b * f)) * ht - f ^ 2 * hA2 - b ^ 2 * hB2
  · refine pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ?_
    linear_combination (-(c * g)) * ht - g ^ 2 * hA2 - c ^ 2 * hB2
  · refine pow_eq_zero_iff (n := 2) two_ne_zero |>.mp ?_
    linear_combination (c * f) * ht - e ^ 2 * hA2 + (b * c) * hB2

private theorem mul_eq_zero_of_trace_mul_eq_zero {m n : Matrix (Fin 2) (Fin 2) F}
    (hm : m * m = 0) (hn : n * n = 0) (ht : (m * n).trace = 0) : m * n = 0 := by
  have hm1 := trace_eq_zero_of_mul_self_eq_zero hm
  have hm2 := det_eq_zero_of_mul_self_eq_zero hm
  have hn1 := trace_eq_zero_of_mul_self_eq_zero hn
  have hn2 := det_eq_zero_of_mul_self_eq_zero hn
  rw [Matrix.trace_fin_two] at hm1 hn1 ht
  rw [Matrix.det_fin_two] at hm2 hn2
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at ht
  obtain ⟨h1, h2, h3, h4⟩ := entries_eq_zero_of_trace hm1 hm2 hn1 hn2 (by linear_combination ht)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    assumption

private theorem mul_add_mul_eq_trace_smul {m n : Matrix (Fin 2) (Fin 2) F} (hm : m.trace = 0)
    (hn : n.trace = 0) : m * n + n * m = (m * n).trace • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.trace_fin_two] at hm hn
  have hd : m 1 1 = -m 0 0 := by linear_combination hm
  have hh : n 1 1 = -n 0 0 := by linear_combination hn
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, hd, hh] <;> ring

end Matrices

section GL2

variable {p : ℕ} [hp : Fact p.Prime]

private theorem sub_one_mul_self_eq_zero {x : GL (Fin 2) (ZMod p)} {k : ℕ} (hx : x ^ p ^ k = 1) :
    ((x : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) * ((x : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) =
      0 := by
  set N := (x : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1 with hN
  have hx' : (1 + N) ^ p ^ k = 1 := by
    have := congrArg (fun u : GL (Fin 2) (ZMod p) => (u : Matrix (Fin 2) (Fin 2) (ZMod p))) hx
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    have e : 1 + N = (x : Matrix (Fin 2) (Fin 2) (ZMod p)) := by rw [hN]; abel
    rwa [e]
  have hNp : N ^ p ^ k = 0 := by
    rw [add_pow_char_pow_of_commute (p := p) (n := k) (Commute.one_left N), one_pow] at hx'
    exact add_eq_left.mp hx'
  have hnil : IsNilpotent N := ⟨_, hNp⟩
  have htr : N.trace = 0 := (Matrix.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  have hdet : N.det = 0 := by
    have := congrArg Matrix.det hNp
    rw [Matrix.det_pow, Matrix.det_zero] at this
    exact pow_eq_zero_iff (pow_ne_zero k hp.out.ne_zero) |>.mp this
  rw [mul_self_fin_two, htr, hdet, zero_smul, zero_smul, sub_self]

theorem commute_of_isSolvable (hp5 : 5 ≤ p) {S : Subgroup (GL (Fin 2) (ZMod p))}
    (hS : Group.IsSolvable S) {x y : GL (Fin 2) (ZMod p)} (hxS : x ∈ S) (hyS : y ∈ S) {k l : ℕ}
    (hx : x ^ p ^ k = 1) (hy : y ^ p ^ l = 1) : Commute x y := by
  classical
  set N₁ := (x : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1 with hN₁
  set N₂ := (y : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1 with hN₂
  have h1 : N₁ * N₁ = 0 := sub_one_mul_self_eq_zero hx
  have h2 : N₂ * N₂ = 0 := sub_one_mul_self_eq_zero hy
  have htr1 := trace_eq_zero_of_mul_self_eq_zero h1
  have htr2 := trace_eq_zero_of_mul_self_eq_zero h2
  have ex : (x : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 + N₁ := by rw [hN₁]; abel
  have ey : (y : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1 + N₂ := by rw [hN₂]; abel
  have hsum := mul_add_mul_eq_trace_smul htr1 htr2
  set t := (N₁ * N₂).trace with ht
  by_cases ht0 : t = 0
  · have h12 : N₁ * N₂ = 0 := mul_eq_zero_of_trace_mul_eq_zero h1 h2 ht0
    have h21 : N₂ * N₁ = 0 := by
      rw [h12, ht0, zero_smul, zero_add] at hsum
      exact hsum
    show x * y = y * x
    apply Units.ext
    simp only [Units.val_mul, ex, ey, mul_add, add_mul, one_mul, mul_one, h12, h21]
    abel
  · exfalso
    have htrace21 : (N₂ * N₁).trace = t := (Matrix.trace_mul_comm N₂ N₁).trans rfl
    have hne : N₂ * N₁ ≠ 0 := fun h => ht0 (by rw [← htrace21, h, Matrix.trace_zero])
    obtain ⟨v, hv⟩ : ∃ v : Fin 2 → ZMod p, (N₂ * N₁) *ᵥ v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hne
      ext i j
      have := congrFun (hcon (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one] using this
    set w₁ := N₁ *ᵥ v with hw₁
    set w₂ := N₂ *ᵥ w₁ with hw₂
    have hw₂0 : w₂ ≠ 0 := by
      rw [hw₂, hw₁, Matrix.mulVec_mulVec]
      exact hv
    have hN1w1 : N₁ *ᵥ w₁ = 0 := by rw [hw₁, Matrix.mulVec_mulVec, h1, Matrix.zero_mulVec]
    have hN2w2 : N₂ *ᵥ w₂ = 0 := by rw [hw₂, Matrix.mulVec_mulVec, h2, Matrix.zero_mulVec]
    have h121 : N₁ * N₂ * N₁ = t • N₁ := by
      have e : N₁ * N₂ = t • 1 - N₂ * N₁ := by rw [← hsum]; abel
      rw [e, sub_mul, smul_mul_assoc, one_mul, mul_assoc, h1, mul_zero]
      simp
    have hN1w2 : N₁ *ᵥ w₂ = t • w₁ := by
      rw [hw₂, hw₁, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h121, Matrix.smul_mulVec]
    have hli : ∀ s s' : ZMod p, s • w₁ + s' • w₂ = 0 → s = 0 ∧ s' = 0 := by
      intro s s' hss'
      have h0 := congrArg (N₂ *ᵥ ·) hss'
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hN2w2, smul_zero, add_zero,
        Matrix.mulVec_zero] at h0
      have hs : s = 0 := (smul_eq_zero.mp h0).resolve_right hw₂0
      rw [hs, zero_smul, zero_add] at hss'
      exact ⟨hs, (smul_eq_zero.mp hss').resolve_right hw₂0⟩
    set P : Matrix (Fin 2) (Fin 2) (ZMod p) := Matrix.of ![![w₁ 0, w₂ 0], ![w₁ 1, w₂ 1]] with hP
    have hPv : ∀ c : Fin 2 → ZMod p, P *ᵥ c = c 0 • w₁ + c 1 • w₂ := by
      intro c
      ext i
      fin_cases i <;> simp [hP, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_comm]
    have hPdet : P.det ≠ 0 := by
      intro hdet
      obtain ⟨c, hc, hPc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
      rw [hPv] at hPc
      obtain ⟨hc0, hc1⟩ := hli _ _ hPc
      apply hc
      ext i
      fin_cases i
      · exact hc0
      · exact hc1
    have c1 := congrFun hN1w1
    have c2 := congrFun hN1w2
    have c3 := congrFun hN2w2
    have c4 : ∀ i, (N₂ *ᵥ w₁) i = w₂ i := fun i => by rw [hw₂]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.zero_apply, Pi.smul_apply,
      smul_eq_mul] at c1 c2 c3 c4
    have hxP : (x : Matrix (Fin 2) (Fin 2) (ZMod p)) * P = P * !![1, t; 0, 1] := by
      rw [ex]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hP, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      · linear_combination c1 0
      · linear_combination c2 0
      · linear_combination c1 1
      · linear_combination c2 1
    have hyP : (y : Matrix (Fin 2) (Fin 2) (ZMod p)) * P = P * !![1, 0; 1, 1] := by
      rw [ey]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hP, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      · linear_combination c4 0
      · linear_combination c3 0
      · linear_combination c4 1
      · linear_combination c3 1
    set Pu := Matrix.GeneralLinearGroup.mkOfDetNeZero P hPdet with hPu
    have hPu' : (Pu : Matrix (Fin 2) (Fin 2) (ZMod p)) = P := rfl
    have hUdet : (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)).det ≠ 0 := by
      have : (!![1, t; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by simp
      rw [this]
      exact one_ne_zero
    have hLdet : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)).det ≠ 0 := by
      have : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by simp
      rw [this]
      exact one_ne_zero
    set Uu := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hUdet with hUu
    set Lu := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hLdet with hLu
    have hxu : x = Pu * Uu * Pu⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hPu', hxP]
      rfl
    have hyu : y = Pu * Lu * Pu⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hPu', hyP]
      rfl
    have hPinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (isUnit_iff_ne_zero.mpr hPdet)
    have hconj : ∀ (a : GL (Fin 2) (ZMod p)) (n : ℕ),
        (((Pu * a * Pu⁻¹) ^ n : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) =
          P * (a : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ n * P⁻¹ := by
      intro a n
      rw [conj_pow, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Matrix.coe_units_inv,
        hPu']
    have hmem : ∀ N : Matrix (Fin 2) (Fin 2) (ZMod p), N.det = 1 →
        ∃ g ∈ Subgroup.closure ({x, y} : Set (GL (Fin 2) (ZMod p))),
          (g : Matrix (Fin 2) (Fin 2) (ZMod p)) = P * N * P⁻¹ := by
      intro N hN
      refine SL2Aux.sl2_induction (fun N => ∃ g ∈ Subgroup.closure
          ({x, y} : Set (GL (Fin 2) (ZMod p))),
          (g : Matrix (Fin 2) (Fin 2) (ZMod p)) = P * N * P⁻¹) ?_ ?_ ?_ N hN
      · rintro A B ⟨g, hg, hgA⟩ ⟨h, hh, hhB⟩
        refine ⟨g * h, Subgroup.mul_mem _ hg hh, ?_⟩
        rw [Units.val_mul, hgA, hhB]
        calc P * A * P⁻¹ * (P * B * P⁻¹) = P * A * (P⁻¹ * P) * B * P⁻¹ := by
              simp only [mul_assoc]
          _ = P * (A * B) * P⁻¹ := by rw [hPinv, mul_one]; simp only [mul_assoc]
      · intro s
        refine ⟨x ^ (s * t⁻¹).val, Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _, ?_⟩
        rw [hxu, hconj, hUu, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, SL2Aux.upper_pow,
          ZMod.natCast_zmod_val, inv_mul_cancel_right₀ ht0]
      · intro s
        refine ⟨y ^ s.val, Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _, ?_⟩
        rw [hyu, hconj, hLu, Matrix.GeneralLinearGroup.val_mkOfDetNeZero, SL2Aux.lower_pow,
          ZMod.natCast_zmod_val, mul_one]
    let φ : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p) :=
      (MulAut.conj Pu).toMonoidHom.comp Matrix.SpecialLinearGroup.toGL
    have hcl : Subgroup.closure ({x, y} : Set (GL (Fin 2) (ZMod p))) ≤ S := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact hxS
      · exact hyS
    have hφS : ∀ M, φ M ∈ S := by
      intro M
      obtain ⟨g, hg, hgM⟩ := hmem M M.2
      have : g = φ M := by
        apply Units.ext
        rw [hgM]
        simp [φ, MulAut.conj_apply, Matrix.coe_units_inv, hPu']
      exact this ▸ hcl hg
    have hinj : Function.Injective φ :=
      (MulAut.conj Pu).injective.comp Matrix.SpecialLinearGroup.toGL_injective
    let ψ : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* S := φ.codRestrict S hφS
    have hψ : Function.Injective ψ := fun a b h => hinj (congrArg Subtype.val h)
    have := hS
    exact not_isSolvable_sl2 hp5 (Group.isSolvable_of_isSolvable_injective hψ)

end GL2

section Aut

theorem not_dvd_card_GL_two {q p : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hqp : q < p) : ¬ p ∣ Nat.card (GL (Fin 2) (ZMod q)) := by
  have hq : q.Prime := Fact.out
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    omega
  rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  have e1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    omega
  have e2 : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_one, sq]
  rw [e1, e2]
  have hle : ∀ n : ℕ, 0 < n → p ∣ n → p ≤ n := fun n hn h => Nat.le_of_dvd hn h
  intro h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h <;> rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · have := hle _ (by omega) h
    omega
  · have h1 := hle _ (by omega) h
    have hpq : p = q + 1 := by omega
    have hqo : Odd q := hq.odd_of_ne_two hq2
    have hpe : Even p := by rw [hpq]; exact hqo.add_one
    exact hp2 ((Nat.Prime.even_iff hp).mp hpe)
  · have := hle _ (by omega) h
    omega
  · have := hle _ (by omega) h
    omega

theorem eq_one_of_pow_prime_pow {M : Type*} [Monoid M] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {g : M} {k m : ℕ} (hk : g ^ p ^ k = 1) (hm : g ^ q ^ m = 1) : g = 1 := by
  have hcop : Nat.Coprime (p ^ k) (q ^ m) :=
    Nat.Coprime.pow k m ((Nat.coprime_primes hp hq).mpr hpq)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk)
    (orderOf_dvd_of_pow_eq_one hm))

theorem eq_one_of_pow_eq_one_of_lt {Q : Type*} [Group Q] [Finite Q] {q p : ℕ} [Fact q.Prime]
    (hq2 : q ≠ 2) (hQ : IsPGroup q Q) (hr : CFSG.Open.pRank q (⊤ : Subgroup Q) ≤ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hqp : q < p) {α : MulAut Q} {k : ℕ} (hα : α ^ p ^ k = 1) :
    α = 1 := by
  have hq : q.Prime := Fact.out
  obtain ⟨φ, hφ⟩ := exists_hom_ker_eq_pCore_aut hq2 hQ hr
  have h1 : φ α = 1 := by
    have hcop : Nat.Coprime (p ^ k) (Nat.card (GL (Fin 2) (ZMod q))) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (not_dvd_card_GL_two hq2 hp hp2 hqp))
    refine orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop ?_ (orderOf_dvd_natCard _))
    exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hα, map_one])
  have h2 : α ∈ CFSG.Open.pCore q (MulAut Q) := by
    rw [← hφ]
    exact h1
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCore_isPGroup q (G := MulAut Q) ⟨α, h2⟩
  have hm' : α ^ q ^ m = 1 := by simpa using congrArg Subtype.val hm
  exact eq_one_of_pow_prime_pow hp hq (fun h => (h ▸ hqp).false) hα hm'

end Aut

end CFSG.Quasithin.EmptyFaithfulMultiple
