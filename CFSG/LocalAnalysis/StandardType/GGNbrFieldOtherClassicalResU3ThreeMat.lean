module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases

public section

namespace CFSG.StandardType

namespace ResU3Three

open Matrix

variable {F : Type*} [Field F]

@[expose] def prj (l : F) (X : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  1 + l ^ 2 • X + l • X ^ 2

theorem mul_prj {l : F} {X : Matrix (Fin 3) (Fin 3) F} (hX : X ^ 3 = 1) (hl : l ^ 3 = 1) :
    X * prj l X = l • prj l X := by
  have h2 : X * X = X ^ 2 := (sq X).symm
  have h3 : X * X ^ 2 = 1 := by
    rw [← hX]
    exact (pow_succ' X 2).symm
  have hl3 : l * l ^ 2 = 1 := by rw [← hl]; ring
  have hl2 : l * l = l ^ 2 := (sq l).symm
  simp only [prj, mul_add, mul_one, Matrix.mul_smul, h2, h3, smul_add, smul_smul, hl3, hl2,
    one_smul]
  abel

theorem prj_add_add [CharP F 2] {c : F} (hc : c ^ 2 + c + 1 = 0) (l : F)
    (X : Matrix (Fin 3) (Fin 3) F) : prj l X + prj (l * c) X + prj (l * c ^ 2) X = 1 := by
  have hc3 : c ^ 3 = 1 := by linear_combination (c - 1) * hc
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e1 : l ^ 2 + (l * c) ^ 2 + (l * c ^ 2) ^ 2 = 0 := by
    linear_combination l ^ 2 * hc + l ^ 2 * c * hc3
  have e2 : l + l * c + l * c ^ 2 = 0 := by linear_combination l * hc
  have e3 : (1 : F) + 1 + 1 = 1 := by linear_combination h2
  have key : prj l X + prj (l * c) X + prj (l * c ^ 2) X =
      ((1 : F) + 1 + 1) • (1 : Matrix (Fin 3) (Fin 3) F) +
        (l ^ 2 + (l * c) ^ 2 + (l * c ^ 2) ^ 2) • X + (l + l * c + l * c ^ 2) • X ^ 2 := by
    simp only [prj, add_smul, one_smul]
    abel
  rw [key, e1, e2, e3, zero_smul, zero_smul, add_zero, add_zero, one_smul]

theorem mul_prj_eq {X Y : Matrix (Fin 3) (Fin 3) F} {ζ : F} (hζ : ζ ^ 3 = 1)
    (hYX : Y * X = ζ • (X * Y)) (l : F) : Y * prj l X = prj (l * ζ ^ 2) X * Y := by
  have hYX2 : Y * X ^ 2 = ζ ^ 2 • (X ^ 2 * Y) := by
    calc Y * X ^ 2 = (Y * X) * X := by rw [sq, mul_assoc]
      _ = (ζ • (X * Y)) * X := by rw [hYX]
      _ = ζ • (X * (Y * X)) := by rw [smul_mul_assoc, mul_assoc]
      _ = ζ • (X * (ζ • (X * Y))) := by rw [hYX]
      _ = ζ ^ 2 • (X ^ 2 * Y) := by
        rw [mul_smul_comm, smul_smul, ← mul_assoc, ← sq, ← sq]
  have hc : (l * ζ ^ 2) ^ 2 = l ^ 2 * ζ := by linear_combination l ^ 2 * ζ * hζ
  simp only [prj, mul_add, add_mul, mul_one, one_mul, Matrix.mul_smul, Matrix.smul_mul, hYX,
    hYX2, smul_smul, hc]

theorem prj_mulVec {X : Matrix (Fin 3) (Fin 3) F} {u : Fin 3 → F} {m : F}
    (hu : X *ᵥ u = m • u) (l : F) : prj l X *ᵥ u = (1 + l ^ 2 * m + l * m ^ 2) • u := by
  have hu2 : X ^ 2 *ᵥ u = m ^ 2 • u := by
    rw [sq, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul, hu, smul_smul, ← sq]
  simp only [prj, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hu, hu2, smul_smul,
    add_smul, one_smul]

theorem one_add_sq_mul_add_mul_sq {a b : F} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : a ≠ b) :
    1 + a ^ 2 * b + a * b ^ 2 = 0 := by
  have hz : a ^ 2 * b - 1 ≠ 0 := by
    intro h
    apply hab
    linear_combination (-a) * h + b * ha
  have h1 : (a ^ 2 * b - 1) * (1 + a ^ 2 * b + a * b ^ 2) = 0 := by
    linear_combination (a * b ^ 2 + b ^ 3) * ha + hb
  exact (mul_eq_zero.mp h1).resolve_left hz

theorem one_add_sq_mul_add_mul_sq_self [CharP F 2] {a : F} (ha : a ^ 3 = 1) :
    1 + a ^ 2 * a + a * a ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination 2 * ha + h2

@[expose] def RegU3Three (M : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∃ (Q : GL (Fin 3) F) (d : Fin 3 → F), Function.Injective d ∧
    M * (Q : Matrix (Fin 3) (Fin 3) F) = (Q : Matrix (Fin 3) (Fin 3) F) * diagonal d

theorem RegU3Three.commute {M N N' : Matrix (Fin 3) (Fin 3) F} (hM : RegU3Three M)
    (hN : N * M = M * N) (hN' : N' * M = M * N') : N * N' = N' * N := by
  obtain ⟨Q, d, hd, hMQ⟩ := hM
  set Qm : Matrix (Fin 3) (Fin 3) F := (Q : Matrix (Fin 3) (Fin 3) F) with hQm
  set Qi : Matrix (Fin 3) (Fin 3) F := ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) with hQi
  have hQQi : Qm * Qi = 1 := by rw [hQm, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hQiQ : Qi * Qm = 1 := by rw [hQm, hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : Qi * M = diagonal d * Qi := by
    calc Qi * M = Qi * M * (Qm * Qi) := by rw [hQQi, mul_one]
      _ = Qi * (M * Qm) * Qi := by simp only [mul_assoc]
      _ = Qi * (Qm * diagonal d) * Qi := by rw [hMQ]
      _ = (Qi * Qm) * diagonal d * Qi := by simp only [mul_assoc]
      _ = diagonal d * Qi := by rw [hQiQ, one_mul]
  have hdiag : ∀ {T : Matrix (Fin 3) (Fin 3) F}, T * M = M * T →
      Qi * T * Qm = diagonal fun i => (Qi * T * Qm) i i := by
    intro T hT
    have key : (Qi * T * Qm) * diagonal d = diagonal d * (Qi * T * Qm) := by
      calc Qi * T * Qm * diagonal d = Qi * T * (M * Qm) := by rw [mul_assoc (Qi * T), hMQ]
        _ = Qi * (T * M) * Qm := by simp only [mul_assoc]
        _ = Qi * (M * T) * Qm := by rw [hT]
        _ = (Qi * M) * T * Qm := by simp only [mul_assoc]
        _ = diagonal d * (Qi * T * Qm) := by rw [h2]; simp only [mul_assoc]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [diagonal_apply_ne _ hij]
      have h := congrFun (congrFun key i) j
      rw [mul_diagonal, diagonal_mul] at h
      have hne : d j - d i ≠ 0 := sub_ne_zero.mpr fun h' => hij (hd h').symm
      have h' : (Qi * T * Qm) i j * (d j - d i) = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_right hne
  have hNd := hdiag hN
  have hN'd := hdiag hN'
  have hback : ∀ T : Matrix (Fin 3) (Fin 3) F, T = Qm * (Qi * T * Qm) * Qi := by
    intro T
    calc T = (Qm * Qi) * T * (Qm * Qi) := by rw [hQQi, one_mul, mul_one]
      _ = Qm * (Qi * T * Qm) * Qi := by simp only [mul_assoc]
  have hcomm : (Qi * N * Qm) * (Qi * N' * Qm) = (Qi * N' * Qm) * (Qi * N * Qm) := by
    rw [hNd, hN'd, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  calc N * N' = Qm * (Qi * N * Qm) * Qi * (Qm * (Qi * N' * Qm) * Qi) := by
        rw [← hback N, ← hback N']
    _ = Qm * ((Qi * N * Qm) * (Qi * N' * Qm)) * Qi := by
        simp only [mul_assoc]
        rw [← mul_assoc Qi Qm, hQiQ, one_mul]
    _ = Qm * ((Qi * N' * Qm) * (Qi * N * Qm)) * Qi := by rw [hcomm]
    _ = Qm * (Qi * N' * Qm) * Qi * (Qm * (Qi * N * Qm) * Qi) := by
        simp only [mul_assoc]
        rw [← mul_assoc Qi Qm, hQiQ, one_mul]
    _ = N' * N := by rw [← hback N, ← hback N']

theorem RegU3Three.smul {M : Matrix (Fin 3) (Fin 3) F} (hM : RegU3Three M) {c : F} (hc : c ≠ 0) :
    RegU3Three (c • M) := by
  obtain ⟨Q, d, hd, hMQ⟩ := hM
  refine ⟨Q, c • d, fun i j h => hd ?_, ?_⟩
  · have h' : c * d i = c * d j := h
    exact mul_left_cancel₀ hc h'
  · rw [smul_mul_assoc, hMQ, diagonal_smul, mul_smul_comm]

theorem RegU3Three.map {F' : Type*} [Field F'] {M : Matrix (Fin 3) (Fin 3) F} (hM : RegU3Three M)
    (j : F →+* F') : RegU3Three (M.map j) := by
  obtain ⟨Q, d, hd, hMQ⟩ := hM
  refine ⟨Matrix.GeneralLinearGroup.map j Q, j ∘ d, j.injective.comp hd, ?_⟩
  have hQ : ((Matrix.GeneralLinearGroup.map j Q : GL (Fin 3) F') : Matrix (Fin 3) (Fin 3) F') =
      (Q : Matrix (Fin 3) (Fin 3) F).map j := rfl
  rw [hQ, ← Matrix.map_mul, hMQ, Matrix.map_mul, diagonal_map (map_zero j)]
  rfl

theorem regU3Three_of_conj {M : Matrix (Fin 3) (Fin 3) F} (Q : GL (Fin 3) F) {d : Fin 3 → F}
    (hd : Function.Injective d)
    (hQ : ((Q⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * M * (Q : Matrix (Fin 3) (Fin 3) F) =
      diagonal d) : RegU3Three M := by
  refine ⟨Q, d, hd, ?_⟩
  rw [← hQ, ← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]

@[expose] def lamU3Three (ω : F) : Fin 3 → F :=
  ![1, ω, ω ^ 2]

theorem lamU3Three_pow_three {ω : F} (hω : ω ^ 2 + ω + 1 = 0) (k : Fin 3) :
    lamU3Three ω k ^ 3 = 1 := by
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  fin_cases k
  · simp [lamU3Three]
  · simpa [lamU3Three] using hω3
  · show (ω ^ 2) ^ 3 = 1
    rw [← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hω3, one_pow]

theorem lamU3Three_injective [CharP F 2] {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    Function.Injective (lamU3Three ω) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h1 : (1 : F) ≠ ω := by
    intro h
    have : (1 : F) = 0 := by linear_combination hω - h2 + (ω + 2) * h
    exact one_ne_zero this
  have h12 : (1 : F) ≠ ω ^ 2 := by
    intro h
    have hω0 : ω = 0 := by linear_combination hω + h - h2
    rw [hω0] at hω
    norm_num at hω
  have h2' : ω ≠ ω ^ 2 := by
    intro h
    have : (1 : F) = 0 := by linear_combination hω + h - ω * h2
    exact one_ne_zero this
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all [lamU3Three, eq_comm]

theorem exists_conj_diag_of_prj_ne_zero [CharP F 2] {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    {X : Matrix (Fin 3) (Fin 3) F} (hX : X ^ 3 = 1)
    (hne : ∀ k : Fin 3, prj (lamU3Three ω k) X ≠ 0) :
    ∃ Q : GL (Fin 3) F,
      X * (Q : Matrix (Fin 3) (Fin 3) F) = (Q : Matrix (Fin 3) (Fin 3) F) *
        diagonal (lamU3Three ω) := by
  classical
  have hl3 := lamU3Three_pow_three hω
  have hinj := lamU3Three_injective hω
  have hcol : ∀ k : Fin 3, ∃ j : Fin 3, (fun i => prj (lamU3Three ω k) X i j) ≠ 0 := by
    intro k
    by_contra h
    push Not at h
    apply hne k
    ext i j
    simpa using congrFun (h j) i
  choose jk hjk using hcol
  set u : Fin 3 → Fin 3 → F := fun k i => prj (lamU3Three ω k) X i (jk k) with hu_def
  have hu : ∀ k, X *ᵥ u k = lamU3Three ω k • u k := by
    intro k
    ext i
    have h := congrFun (congrFun (mul_prj hX (hl3 k)) i) (jk k)
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hu_def] using h
  have hproj : ∀ k k', prj (lamU3Three ω k) X *ᵥ u k' = (if k = k' then (1 : F) else 0) • u k' := by
    intro k k'
    rw [prj_mulVec (hu k')]
    split_ifs with h
    · subst h
      rw [one_add_sq_mul_add_mul_sq_self (hl3 k)]
    · rw [one_add_sq_mul_add_mul_sq (hl3 k) (hl3 k') fun h' => h (hinj h')]
  set Q₀ : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i k => u k i with hQ₀
  have hQv : ∀ c : Fin 3 → F, Q₀ *ᵥ c = ∑ k, c k • u k := by
    intro c
    ext i
    simp [hQ₀, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hdet : Q₀.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hc0
    funext k
    have h1 := congrArg (fun v => prj (lamU3Three ω k) X *ᵥ v) hc
    simp only [hQv, Matrix.mulVec_sum, Matrix.mulVec_smul, hproj, smul_smul, Matrix.mulVec_zero]
      at h1
    rw [Finset.sum_eq_single k (fun b _ hb => by rw [if_neg (Ne.symm hb), mul_zero, zero_smul])
      (fun h => absurd (Finset.mem_univ k) h), if_pos rfl, mul_one] at h1
    by_contra hck
    exact hjk k (by
      have := congrArg (fun v => (c k)⁻¹ • v) h1
      simpa [smul_smul, inv_mul_cancel₀ hck, hu_def] using this)
  refine ⟨Matrix.nonsingInvUnit Q₀ (isUnit_iff_ne_zero.mpr hdet), ?_⟩
  show X * Q₀ = Q₀ * diagonal (lamU3Three ω)
  ext i k
  rw [mul_diagonal]
  have h := congrFun (hu k) i
  simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, hQ₀, mul_comm] using h

theorem regU3Three_of_prj_ne_zero [CharP F 2] {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    {X : Matrix (Fin 3) (Fin 3) F} (hX : X ^ 3 = 1)
    (hne : ∀ k : Fin 3, prj (lamU3Three ω k) X ≠ 0) : RegU3Three X := by
  obtain ⟨Q, hQ⟩ := exists_conj_diag_of_prj_ne_zero hω hX hne
  exact ⟨Q, lamU3Three ω, lamU3Three_injective hω, hQ⟩

theorem regU3Three_of_partner [CharP F 2] {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    {X Y : Matrix (Fin 3) (Fin 3) F} (hX : X ^ 3 = 1) (hY : IsUnit Y) {ζ : F}
    (hζ : ζ ^ 2 + ζ + 1 = 0) (hYX : Y * X = ζ • (X * Y)) : RegU3Three X := by
  have hζ3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * hζ
  obtain ⟨Yu, rfl⟩ := hY
  have hzero : ∀ l : F, prj l X = 0 → prj (l * ζ ^ 2) X = 0 := by
    intro l hl
    have h1 := mul_prj_eq hζ3 hYX l
    rw [hl, mul_zero] at h1
    have h2 := congrArg (fun T => T * ((Yu⁻¹ : (Matrix (Fin 3) (Fin 3) F)ˣ) :
      Matrix (Fin 3) (Fin 3) F)) h1
    simp only [zero_mul, mul_assoc, Units.mul_inv, mul_one] at h2
    exact h2.symm
  refine regU3Three_of_prj_ne_zero hω hX fun k hk => ?_
  have h1 := hzero _ hk
  have h2 := hzero _ h1
  have e : lamU3Three ω k * ζ ^ 2 * ζ ^ 2 = lamU3Three ω k * ζ := by
    linear_combination lamU3Three ω k * ζ * hζ3
  rw [e] at h2
  have hsum := prj_add_add hζ (lamU3Three ω k) X
  rw [hk, h1, h2, add_zero, add_zero] at hsum
  exact one_ne_zero hsum.symm

theorem regU3Three_of_not_cube {F' : Type*} [Field F'] [CharP F' 2] (j : F →+* F') {ω : F}
    (hω : ω ^ 2 + ω + 1 = 0) {B : Matrix (Fin 3) (Fin 3) F} {s : F}
    (hB : B ^ 3 = s • (1 : Matrix (Fin 3) (Fin 3) F)) (hs : ∀ e : F, e ^ 3 ≠ s) {e : F'}
    (he : e ^ 3 = j s) : RegU3Three (B.map j) := by
  classical
  have he0 : e ≠ 0 := by
    rintro rfl
    have h0 : j s = 0 := by rw [← he]; ring
    rw [map_eq_zero] at h0
    exact hs 0 (by rw [h0]; ring)
  have hmapPow : ∀ (M : Matrix (Fin 3) (Fin 3) F) (k : ℕ), (M.map j) ^ k = (M ^ k).map j := by
    intro M k
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
  set X : Matrix (Fin 3) (Fin 3) F' := e⁻¹ • B.map j with hXdef
  have hBj : (B.map j) ^ 3 = j s • (1 : Matrix (Fin 3) (Fin 3) F') := by
    rw [hmapPow, hB]
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · simp [Matrix.one_apply_ne hab]
  have hX : X ^ 3 = 1 := by
    rw [hXdef, smul_pow, hBj, smul_smul, ← he, ← mul_pow, inv_mul_cancel₀ he0, one_pow,
      one_smul]
  have hωj : (j ω) ^ 2 + j ω + 1 = 0 := by
    rw [← map_pow, ← map_one j, ← map_add, ← map_add, hω, map_zero]
  have hlam : ∀ k, lamU3Three (j ω) k = j (lamU3Three ω k) := by
    intro k
    fin_cases k <;> simp [lamU3Three]
  have hscale : ∀ l : F', e ^ 2 • prj l X =
      e ^ 2 • (1 : Matrix (Fin 3) (Fin 3) F') + (l ^ 2 * e) • B.map j + l • (B ^ 2).map j := by
    intro l
    have c1 : e ^ 2 * l ^ 2 * e⁻¹ = l ^ 2 * e := by field_simp
    have c2 : e ^ 2 * l * (e⁻¹) ^ 2 = l := by field_simp
    rw [prj, hXdef, smul_pow, ← hmapPow, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
      smul_smul, c1, c2]
  have hne : ∀ k, prj (lamU3Three (j ω) k) X ≠ 0 := by
    intro k hk
    set l₀ := lamU3Three ω k with hl₀def
    have hl₀ : l₀ ^ 3 = 1 := lamU3Three_pow_three hω k
    have hl3 : (j l₀) ^ 3 = 1 := by rw [← map_pow, hl₀, map_one]
    rw [hlam k] at hk
    have hz := hscale (j l₀)
    rw [hk, smul_zero] at hz
    by_cases hoff : ∃ u v : Fin 3, u ≠ v ∧ B u v ≠ 0
    · obtain ⟨u, v, huv, hBuv⟩ := hoff
      have h1 := congrFun (congrFun hz u) v
      simp only [Matrix.zero_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne huv,
        Matrix.map_apply, smul_eq_mul, mul_zero, zero_add] at h1
      have hjB : j (B u v) ≠ 0 := (map_ne_zero j).mpr hBuv
      have h2 : e * j (B u v) + j l₀ ^ 2 * j ((B ^ 2) u v) = 0 := by
        linear_combination -(j l₀) * h1 - (e * j (B u v)) * hl3
      apply hs (-(l₀ ^ 2 * (B ^ 2) u v) / B u v)
      apply j.injective
      rw [map_pow, ← he]
      congr 1
      rw [map_div₀, map_neg, map_mul, map_pow, div_eq_iff hjB]
      linear_combination -h2
    · push Not at hoff
      have hBd : B = diagonal fun i => B i i := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp
        · rw [diagonal_apply_ne _ hab]
          exact hoff a b hab
      apply hs (B 0 0)
      have h3 := congrFun (congrFun hB 0) 0
      rw [hBd, diagonal_pow] at h3
      simpa using h3
  have hBX : B.map j = e • X := by
    rw [hXdef, smul_smul, mul_inv_cancel₀ he0, one_smul]
  rw [hBX]
  exact (regU3Three_of_prj_ne_zero hωj hX hne).smul he0

theorem fin_three_cases_U3Three : ∀ u v : Fin 3, u ≠ v →
    ∃ w : Fin 3, w ≠ u ∧ w ≠ v ∧ ∀ i : Fin 3, i = u ∨ i = v ∨ i = w := by
  decide

theorem not_forall_swap_U3Three {G : Type*} [CommGroup G] {d : Fin 3 → G}
    (hd : ¬ Function.Injective d) {u v : Fin 3} (huv : d u ≠ d v) (z : G) (m : ℤ) :
    ¬ ∀ i, d (Equiv.swap u v i) = z * d i ^ m := by
  intro h
  have huv' : u ≠ v := fun h' => huv (by rw [h'])
  obtain ⟨w, hwu, hwv, hall⟩ := fin_three_cases_U3Three u v huv'
  have hu := h u
  have hv := h v
  have hw := h w
  rw [Equiv.swap_apply_left] at hu
  rw [Equiv.swap_apply_right] at hv
  rw [Equiv.swap_apply_of_ne_of_ne hwu hwv] at hw
  obtain ⟨x, y, hxy, hxy'⟩ : ∃ x y, d x = d y ∧ x ≠ y := by
    by_contra hc
    push Not at hc
    exact hd fun a b hab => hc a b hab
  have hw' : d w = d u ∨ d w = d v := by
    rcases hall x with rfl | rfl | rfl <;> rcases hall y with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hxy'
      | exact absurd hxy huv
      | exact absurd hxy.symm huv
      | exact Or.inl hxy.symm
      | exact Or.inl hxy
      | exact Or.inr hxy.symm
      | exact Or.inr hxy
  rcases hw' with hwu' | hwv'
  · apply huv
    rw [hu, ← hwu', ← hw]
  · apply huv
    rw [hv, ← hwv', ← hw]

theorem exists_odd_U3Three {α : Type*} {d : Fin 3 → α} (hd : ¬ Function.Injective d)
    (hc : ∃ a b, d a ≠ d b) : ∃ i, ∀ j, j ≠ i → d j ≠ d i := by
  obtain ⟨x, y, hxy, hxy'⟩ : ∃ x y, d x = d y ∧ x ≠ y := by
    by_contra hc'
    push Not at hc'
    exact hd fun a b hab => hc' a b hab
  obtain ⟨w, hwx, hwy, hall⟩ := fin_three_cases_U3Three x y hxy'
  have hwne : d w ≠ d x := by
    intro hw
    obtain ⟨a, b, hab⟩ := hc
    apply hab
    rcases hall a with rfl | rfl | rfl <;> rcases hall b with rfl | rfl | rfl <;>
      simp_all
  refine ⟨w, fun i hi => ?_⟩
  rcases hall i with rfl | rfl | rfl
  · exact fun h => hwne h.symm
  · rw [← hxy]
    exact fun h => hwne h.symm
  · exact absurd rfl hi

end ResU3Three

end CFSG.StandardType

end
