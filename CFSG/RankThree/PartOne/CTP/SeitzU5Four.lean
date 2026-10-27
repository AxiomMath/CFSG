module

public import CFSG.RankThree.PartOne.CTP.SeitzU5Gen
public import CFSG.RankThree.PartOne.CTP.SeitzU5Eigen

public section

namespace CFSG.RankThree.PartOne.CTP.U5Four

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution.Phan CFSG.LieType.BorelTits CFSG.RankThree.PartOne.CTP.U5Gen

section Model

abbrev G16 := Fin 4 → ZMod 2

@[expose] def wpow (n : ℕ) : G16 :=
  match n % 5 with
  | 0 => ![1, 0, 0, 0]
  | 1 => ![0, 1, 0, 0]
  | 2 => ![0, 0, 1, 0]
  | 3 => ![0, 0, 0, 1]
  | _ => ![1, 1, 1, 1]

@[expose] def gmul (a b : G16) : G16 := ![
  a 0 * b 0 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 2 * b 3 + a 3 * b 2,
  a 0 * b 1 + a 1 * b 0 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1 + a 3 * b 3,
  a 0 * b 2 + a 1 * b 1 + a 2 * b 0 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1,
  a 0 * b 3 + a 1 * b 2 + a 2 * b 1 + a 3 * b 0 + a 1 * b 3 + a 2 * b 2 + a 3 * b 1]

@[expose] def gconj (a : G16) : G16 :=
  ![a 0 + a 1, a 1, a 1 + a 3, a 1 + a 2]

abbrev M5 := Fin 5 → Fin 5 → G16

@[expose] def gmm (A B : M5) : M5 := fun i j =>
  gmul (A i 0) (B 0 j) + gmul (A i 1) (B 1 j) + gmul (A i 2) (B 2 j) + gmul (A i 3) (B 3 j) +
    gmul (A i 4) (B 4 j)

@[expose] def gconjT (A : M5) : M5 := fun i j => gconj (A j i)

@[expose] def I5 : M5 := fun i j => if i = j then ![1, 0, 0, 0] else 0

@[expose] def diagG (e : Fin 5 → ℕ) : M5 := fun i j => if i = j then wpow (e i) else 0

@[expose] def Fg : M5 := fun j k => wpow ((j : ℕ) * (k : ℕ))

@[expose] def Finvg : M5 := fun j k => wpow (4 * ((j : ℕ) * (k : ℕ)))

@[expose] def Sg : M5 := fun s k => if k = s - 1 then ![1, 0, 0, 0] else 0

@[expose] def tvG (c : G16) : M5 :=
  fun i j => I5 i j + (if 3 ≤ (i : ℕ) ∧ 3 ≤ (j : ℕ) then c else 0)

@[expose] def letterE : Fin 16 → Fin 5 → ℕ := ![
  ![1, 4, 0, 0, 0], ![0, 1, 4, 0, 0], ![0, 0, 1, 4, 0], ![0, 0, 0, 1, 4],
  ![1, 4, 0, 0, 0], ![0, 1, 4, 0, 0], ![0, 0, 1, 4, 0], ![0, 0, 0, 1, 4],
  ![4, 1, 0, 0, 0], ![0, 4, 1, 0, 0], ![0, 0, 4, 1, 0], ![0, 0, 0, 4, 1],
  ![4, 1, 0, 0, 0], ![0, 4, 1, 0, 0], ![0, 0, 4, 1, 0], ![0, 0, 0, 4, 1]]

@[expose] def letterT (k : Fin 16) : Bool := decide (4 ≤ (k : ℕ) % 8)

@[expose] def letterG (k : Fin 16) : M5 :=
  if letterT k then gmm (gmm Fg (diagG (letterE k))) Finvg else diagG (letterE k)

@[expose] def evalW (w : List (Fin 16)) : M5 := w.foldl (fun A k => gmm A (letterG k)) I5

@[expose] def W1 : List (Fin 16) := [14, 3, 3, 5, 0, 13]

@[expose] def W2 : List (Fin 16) := [2, 12, 9, 6, 8, 8, 13]

@[expose] def Bg : M5 := ![
  ![![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
  ![![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0]],
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 1, 1], ![1, 0, 0, 1]],
  ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0], ![1, 0, 1, 0], ![0, 0, 1, 1]]]

end Model

section Checks

theorem check_FFinv : gmm Fg Finvg = I5 := by decide +kernel

theorem check_Fconj : gconjT Fg = Finvg := by decide +kernel

theorem check_S : gmm (gmm Fg (diagG ![0, 4, 3, 2, 1])) Finvg = Sg := by decide +kernel

theorem check_word : evalW W2 = gmm (evalW W1) Bg := by decide +kernel

theorem check_tv1 : gmm (gmm (gmm (gmm (letterG 11) (letterG 11)) Bg) (letterG 3)) (letterG 3) =
    tvG ![1, 0, 1, 1] := by decide +kernel

theorem check_tv2 : gmm (gmm (gmm (gmm (letterG 3) Bg) (letterG 3)) (letterG 3)) Bg =
    tvG ![0, 0, 1, 1] := by decide +kernel

theorem letterE_sum : ∀ k : Fin 16, (∑ i, letterE k i) % 5 = 0 := by decide +kernel

end Checks

section Val

variable {K : Type} [Field K] [CharP K 2] (ω : K)

@[expose] def valHom : G16 →+ K where
  toFun a := ∑ i : Fin 4, (ZMod.castHom (dvd_refl 2) K (a i)) * ω ^ (i : ℕ)
  map_zero' := by simp
  map_add' a b := by
    simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

@[expose] def val (a : G16) : K := valHom ω a

theorem val_eq (a : G16) : val ω a =
    (ZMod.castHom (dvd_refl 2) K (a 0)) + (ZMod.castHom (dvd_refl 2) K (a 1)) * ω +
      (ZMod.castHom (dvd_refl 2) K (a 2)) * ω ^ 2 +
        (ZMod.castHom (dvd_refl 2) K (a 3)) * ω ^ 3 := by
  simp [val, valHom, Fin.sum_univ_four]

theorem val_add (a b : G16) : val ω (a + b) = val ω a + val ω b := map_add (valHom ω) a b

variable {ω} (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
include hω

theorem pow_five : ω ^ 5 = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (ω - 1) * hω

theorem val_wpow (n : ℕ) : val ω (wpow n) = ω ^ n := by
  have h5 := pow_five hω
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hn : ω ^ n = ω ^ (n % 5) := by
    conv_lhs => rw [← Nat.mod_add_div n 5, pow_add, pow_mul, h5, one_pow, mul_one]
  rw [hn, wpow]
  have : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 5 <;> simp [val_eq]
  linear_combination hω - ω ^ 4 * h2

theorem val_gmul (a b : G16) : val ω (gmul a b) = val ω a * val ω b := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hw4 : ω ^ 4 = 1 + ω + ω ^ 2 + ω ^ 3 := by
    linear_combination hω - (1 + ω + ω ^ 2 + ω ^ 3) * h2
  have hw5 : ω ^ 5 = 1 := pow_five hω
  have hw6 : ω ^ 6 = ω := by linear_combination ω * hw5
  simp only [val_eq, gmul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    map_add, map_mul]
  set α0 := ZMod.castHom (dvd_refl 2) K (a 0)
  set α1 := ZMod.castHom (dvd_refl 2) K (a 1)
  set α2 := ZMod.castHom (dvd_refl 2) K (a 2)
  set α3 := ZMod.castHom (dvd_refl 2) K (a 3)
  set β0 := ZMod.castHom (dvd_refl 2) K (b 0)
  set β1 := ZMod.castHom (dvd_refl 2) K (b 1)
  set β2 := ZMod.castHom (dvd_refl 2) K (b 2)
  set β3 := ZMod.castHom (dvd_refl 2) K (b 3)
  linear_combination (-(α1 * β3 + α2 * β2 + α3 * β1)) * hw4 + (-(α2 * β3 + α3 * β2)) * hw5 +
    (-(α3 * β3)) * hw6

theorem val_gconj (σ : K ≃+* K) (hσ : σ ω = ω ^ 4) (a : G16) :
    val ω (gconj a) = σ (val ω a) := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hw4 : ω ^ 4 = 1 + ω + ω ^ 2 + ω ^ 3 := by
    linear_combination hω - (1 + ω + ω ^ 2 + ω ^ 3) * h2
  have hw5 : ω ^ 5 = 1 := pow_five hω
  have hw8 : ω ^ 8 = ω ^ 3 := by linear_combination ω ^ 3 * hw5
  have hw12 : ω ^ 12 = ω ^ 2 := by linear_combination (ω ^ 7 + ω ^ 2) * hw5
  have hc : ∀ c : ZMod 2, σ (ZMod.castHom (dvd_refl 2) K c) = ZMod.castHom (dvd_refl 2) K c := by
    intro c
    have := RingHom.ext_zmod ((σ : K →+* K).comp (ZMod.castHom (dvd_refl 2) K))
      (ZMod.castHom (dvd_refl 2) K)
    exact congrArg (fun φ => φ c) this
  simp only [val_eq, gconj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, map_add,
    map_mul, map_pow, hc, hσ]
  set α1 := ZMod.castHom (dvd_refl 2) K (a 1)
  set α2 := ZMod.castHom (dvd_refl 2) K (a 2)
  set α3 := ZMod.castHom (dvd_refl 2) K (a 3)
  linear_combination (-α1) * hw4 + (-α2) * hw8 + (-α3) * hw12

end Val

section Mat

variable {K : Type} [Field K] [CharP K 2] {ω : K}

@[expose] def valMat (ω : K) (A : M5) : Matrix (Fin 5) (Fin 5) K :=
  Matrix.of fun i j => val ω (A i j)

theorem valMat_gmm (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (A B : M5) :
    valMat ω (gmm A B) = valMat ω A * valMat ω B := by
  ext i j
  simp only [valMat, gmm, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_five, val_add,
    val_gmul hω]

theorem valMat_I5 : valMat ω I5 = 1 := by
  ext i j
  by_cases h : i = j
  · subst h; simp [valMat, I5, val_eq]
  · simp [valMat, I5, h, val_eq]

theorem valMat_diagG (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (e : Fin 5 → ℕ) :
    valMat ω (diagG e) = Matrix.diagonal (fun i => ω ^ e i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [valMat, diagG, val_wpow hω]
  · simp [valMat, diagG, h, val_eq]

theorem valMat_gconjT (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (σ : K ≃+* K)
    (hσ : σ ω = ω ^ 4) (A : M5) : valMat ω (gconjT A) = conjTr σ (valMat ω A) := by
  ext i j
  simp [valMat, gconjT, conjTr, val_gconj hω σ hσ]

theorem valMat_tvG (σ : K ≃+* K) (hσ1 : σ 1 = 1) (c : G16) :
    valMat ω (tvG c) = tvMat σ (![0, 0, 0, 1, 1] : Fin 5 → K) (val ω c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [valMat, tvG, I5, tvMat, vecMulVec, val_eq, hσ1] <;> ring

theorem valMat_Sg : valMat ω Sg = U5Eigen.shiftMat := by
  ext s k
  rw [U5Eigen.shiftMat_apply]
  by_cases h : k = s - 1
  · simp [valMat, Sg, h, val_eq]
  · simp [valMat, Sg, h, val_eq]

end Mat

section Group

variable {K : Type} [Field K] [Finite K] [CharP K 2] {ω : K}

local notation "σ₄" => unitaryInvolution K 2 2

theorem sigma_omega (ω : K) : σ₄ ω = ω ^ 4 := by
  rw [unitaryInvolution_apply]
  norm_num

theorem norm_omega_pow (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (m : ℕ) :
    σ₄ (ω ^ m) * ω ^ m = 1 := by
  rw [map_pow, sigma_omega, ← pow_mul, ← pow_add]
  have h5 := pow_five hω
  have : 4 * m + m = 5 * m := by ring
  rw [this, pow_mul, h5, one_pow]

@[expose] noncomputable def dgW (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (e : Fin 5 → ℕ)
    (he : (∑ i, e i) % 5 = 0) : SUid σ₄ 5 :=
  dgSU σ₄ (fun i => ω ^ e i) (fun i => norm_omega_pow hω (e i)) (by
    rw [Finset.prod_pow_eq_pow_sum]
    obtain ⟨m, hm⟩ : 5 ∣ ∑ i, e i := Nat.dvd_of_mod_eq_zero he
    rw [hm, pow_mul, pow_five hω, one_pow])

theorem mat_dgW (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (e : Fin 5 → ℕ)
    (he : (∑ i, e i) % 5 = 0) :
    mat σ₄ (dgW hω e he) = Matrix.diagonal (fun i => ω ^ e i) := rfl

section Fourier

theorem conjTr_conjTr (hK : Nat.card K = (2 ^ 2) ^ 2) (A : Matrix (Fin 5) (Fin 5) K) :
    conjTr σ₄ (conjTr σ₄ A) = A := by
  ext i j
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply]
  exact unitaryInvolution_involutive hK _

omit [Finite K] in
theorem hFF (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : valMat ω Fg * valMat ω Finvg = 1 := by
  rw [← valMat_gmm hω, check_FFinv, valMat_I5]

theorem hFF' (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : valMat ω Finvg * valMat ω Fg = 1 :=
  mul_eq_one_comm.mp (hFF hω)

theorem hFc (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    conjTr σ₄ (valMat ω Fg) = valMat ω Finvg := by
  rw [← valMat_gconjT hω σ₄ (sigma_omega ω), check_Fconj]

theorem hFc' (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    conjTr σ₄ (valMat ω Finvg) = valMat ω Fg := by
  rw [← hFc hω, conjTr_conjTr hK]

theorem conjF_aux (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (G : Matrix (Fin 5) (Fin 5) K) (hG : conjTr σ₄ G * G = 1) :
    conjTr σ₄ (valMat ω Fg * G * valMat ω Finvg) * (valMat ω Fg * G * valMat ω Finvg) = 1 := by
  rw [conjTr_mul, conjTr_mul, hFc hω, hFc' hK hω]
  calc (valMat ω Fg * (conjTr σ₄ G * valMat ω Finvg)) *
        (valMat ω Fg * G * valMat ω Finvg)
      = valMat ω Fg * (conjTr σ₄ G * (valMat ω Finvg * valMat ω Fg) * G) * valMat ω Finvg := by
        simp only [Matrix.mul_assoc]
    _ = valMat ω Fg * (conjTr σ₄ G * G) * valMat ω Finvg := by rw [hFF' hω, Matrix.mul_one]
    _ = 1 := by rw [hG, Matrix.mul_one, hFF hω]

@[expose] noncomputable def conjF (hK : Nat.card K = (2 ^ 2) ^ 2)
    (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (g : SUid σ₄ 5) : SUid σ₄ 5 :=
  mkSU σ₄ (valMat ω Fg * mat σ₄ g * valMat ω Finvg) (by
    have h1 : (mat σ₄ g).det = 1 := g.2.1
    rw [Matrix.det_mul, Matrix.det_mul, h1, mul_one, ← Matrix.det_mul, hFF hω, Matrix.det_one])
    (by
      intro x y
      have h1 : conjTr σ₄ (mat σ₄ g) * mat σ₄ g = 1 := g.2.2
      rw [herm_mulVec, conjF_aux hK hω _ h1, Matrix.one_mulVec])

theorem mat_conjF (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (g : SUid σ₄ 5) :
    mat σ₄ (conjF hK hω g) = valMat ω Fg * mat σ₄ g * valMat ω Finvg := rfl

theorem conjF_mul (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (g h : SUid σ₄ 5) : conjF hK hω (g * h) = conjF hK hω g * conjF hK hω h := by
  apply Subtype.ext
  apply Units.ext
  show valMat ω Fg * mat σ₄ (g * h) * valMat ω Finvg =
    (valMat ω Fg * mat σ₄ g * valMat ω Finvg) * (valMat ω Fg * mat σ₄ h * valMat ω Finvg)
  rw [mat_mul]
  calc valMat ω Fg * (mat σ₄ g * mat σ₄ h) * valMat ω Finvg
      = valMat ω Fg * mat σ₄ g * (valMat ω Finvg * valMat ω Fg) * mat σ₄ h * valMat ω Finvg := by
        rw [hFF' hω, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

section Letters

theorem sigma_apply (c : K) : σ₄ c = c ^ 4 := by
  rw [unitaryInvolution_apply]
  norm_num

omit [CharP K 2] in
theorem exists_omega (hK : Nat.card K = (2 ^ 2) ^ 2) :
    ∃ ω : K, ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 15 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
    norm_num
  have hgK : orderOf (g : K) = 15 := by rw [orderOf_units, hord]
  have hω : orderOf ((g : K) ^ 3) = 5 := by
    rw [orderOf_pow' _ (by norm_num : 3 ≠ 0), hgK]
    norm_num
  have h5 : ((g : K) ^ 3) ^ 5 = 1 := by
    have := pow_orderOf_eq_one ((g : K) ^ 3)
    rwa [hω] at this
  have h1 : (g : K) ^ 3 - 1 ≠ 0 := by
    intro h
    have : (g : K) ^ 3 = 1 := sub_eq_zero.mp h
    rw [this, orderOf_one] at hω
    omega
  refine ⟨(g : K) ^ 3, ?_⟩
  have : ((g : K) ^ 3 - 1) * (((g : K) ^ 3) ^ 4 + ((g : K) ^ 3) ^ 3 + ((g : K) ^ 3) ^ 2 +
      (g : K) ^ 3 + 1) = 0 := by linear_combination h5
  exact (mul_eq_zero.mp this).resolve_left h1

@[expose] noncomputable def letterEl (hK : Nat.card K = (2 ^ 2) ^ 2)
    (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (k : Fin 16) : SUid σ₄ 5 :=
  if letterT k = true then conjF hK hω (dgW hω (letterE k) (letterE_sum k))
  else dgW hω (letterE k) (letterE_sum k)

theorem mat_letterEl (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (k : Fin 16) : mat σ₄ (letterEl hK hω k) = valMat ω (letterG k) := by
  by_cases hk : letterT k = true
  · simp only [letterEl, letterG, hk, ite_true]
    rw [mat_conjF, mat_dgW, valMat_gmm hω, valMat_gmm hω, valMat_diagG hω]
  · have hk' : letterT k = false := by simpa using hk
    simp only [letterEl, letterG, hk', Bool.false_eq_true, ite_false]
    rw [mat_dgW, valMat_diagG hω]

theorem circ_comm (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (D L : Matrix (Fin 5) (Fin 5) K)
    (hDL : D * L = L * D) :
    (valMat ω Fg * D * valMat ω Finvg) * (valMat ω Fg * L * valMat ω Finvg) =
      (valMat ω Fg * L * valMat ω Finvg) * (valMat ω Fg * D * valMat ω Finvg) := by
  calc (valMat ω Fg * D * valMat ω Finvg) * (valMat ω Fg * L * valMat ω Finvg)
      = valMat ω Fg * (D * L) * valMat ω Finvg := by
        have := hFF' hω
        calc _ = valMat ω Fg * D * (valMat ω Finvg * valMat ω Fg) * L * valMat ω Finvg := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [this, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = valMat ω Fg * (L * D) * valMat ω Finvg := by rw [hDL]
    _ = _ := by
        have := hFF' hω
        calc _ = valMat ω Fg * L * (valMat ω Finvg * valMat ω Fg) * D * valMat ω Finvg := by
              rw [this, Matrix.mul_one]; simp only [Matrix.mul_assoc]
          _ = _ := by simp only [Matrix.mul_assoc]

omit [Finite K] in
theorem valMat_Sg_eq (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    valMat ω Sg = valMat ω Fg * Matrix.diagonal (fun i => ω ^ (![0, 4, 3, 2, 1] : Fin 5 → ℕ) i) *
      valMat ω Finvg := by
  rw [← check_S, valMat_gmm hω, valMat_gmm hω, valMat_diagG hω]

theorem letterEl_mem (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (M : Subgroup (SUid σ₄ 5))
    (hD : ∀ (t : Fin 5 → K) (ht : ∀ i, σ₄ (t i) * t i = 1) (hdet : ∏ i, t i = 1),
      dgSU σ₄ t ht hdet ∈ M)
    (hC : ∀ g : SUid σ₄ 5, mat σ₄ g * valMat ω Sg = valMat ω Sg * mat σ₄ g → g ∈ M)
    (k : Fin 16) : letterEl hK hω k ∈ M := by
  by_cases hk : letterT k = true
  · simp only [letterEl, hk, ite_true]
    refine hC _ ?_
    rw [mat_conjF, mat_dgW, valMat_Sg_eq hω]
    refine circ_comm hω _ _ ?_
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · have hk' : letterT k = false := by simpa using hk
    simp only [letterEl, hk', Bool.false_eq_true, ite_false]
    exact hD _ _ _

end Letters

end Fourier

section Words

@[expose] noncomputable def wordEl (hK : Nat.card K = (2 ^ 2) ^ 2)
    (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (w : List (Fin 16)) : SUid σ₄ 5 :=
  w.foldl (fun B k => B * letterEl hK hω k) 1

theorem mat_foldl (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (w : List (Fin 16)) (acc : SUid σ₄ 5) (A : M5) (h : mat σ₄ acc = valMat ω A) :
    mat σ₄ (w.foldl (fun B k => B * letterEl hK hω k) acc) =
      valMat ω (w.foldl (fun B k => gmm B (letterG k)) A) := by
  induction w generalizing acc A with
  | nil => simpa using h
  | cons k w ih =>
    simp only [List.foldl_cons]
    refine ih _ _ ?_
    rw [mat_mul, h, mat_letterEl hK hω, valMat_gmm hω]

theorem mat_wordEl (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (w : List (Fin 16)) : mat σ₄ (wordEl hK hω w) = valMat ω (evalW w) := by
  refine mat_foldl hK hω w 1 I5 ?_
  rw [valMat_I5]
  rfl

theorem wordEl_mem (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (M : Subgroup (SUid σ₄ 5)) (hL : ∀ k, letterEl hK hω k ∈ M) (w : List (Fin 16)) :
    wordEl hK hω w ∈ M := by
  suffices H : ∀ (w : List (Fin 16)) (acc : SUid σ₄ 5), acc ∈ M →
      w.foldl (fun B k => B * letterEl hK hω k) acc ∈ M from H w 1 M.one_mem
  intro w
  induction w with
  | nil => intro acc hacc; exact hacc
  | cons k w ih => intro acc hacc; exact ih _ (M.mul_mem hacc (hL k))

@[expose] noncomputable def blockEl (hK : Nat.card K = (2 ^ 2) ^ 2)
    (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : SUid σ₄ 5 :=
  (wordEl hK hω W1)⁻¹ * wordEl hK hω W2

theorem mat_blockEl (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    mat σ₄ (blockEl hK hω) = valMat ω Bg := by
  have h1 : mat σ₄ (wordEl hK hω W2) = mat σ₄ (wordEl hK hω W1) * valMat ω Bg := by
    rw [mat_wordEl, mat_wordEl, check_word, valMat_gmm hω]
  have h2 : mat σ₄ ((wordEl hK hω W1)⁻¹) * mat σ₄ (wordEl hK hω W1) = 1 := by
    rw [← mat_mul, inv_mul_cancel]
    rfl
  rw [blockEl, mat_mul, h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem blockEl_mem (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0)
    (M : Subgroup (SUid σ₄ 5)) (hL : ∀ k, letterEl hK hω k ∈ M) : blockEl hK hω ∈ M :=
  M.mul_mem (M.inv_mem (wordEl_mem hK hω M hL W1)) (wordEl_mem hK hω M hL W2)

@[expose] noncomputable def tvEl1 (hK : Nat.card K = (2 ^ 2) ^ 2)
    (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : SUid σ₄ 5 :=
  letterEl hK hω 11 * letterEl hK hω 11 * blockEl hK hω * letterEl hK hω 3 * letterEl hK hω 3

@[expose] noncomputable def tvEl2 (hK : Nat.card K = (2 ^ 2) ^ 2)
    (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) : SUid σ₄ 5 :=
  letterEl hK hω 3 * blockEl hK hω * letterEl hK hω 3 * letterEl hK hω 3 * blockEl hK hω

theorem mat_tvEl1 (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    mat σ₄ (tvEl1 hK hω) = valMat ω (tvG ![1, 0, 1, 1]) := by
  simp only [tvEl1, mat_mul, mat_letterEl hK hω, mat_blockEl hK hω]
  rw [← check_tv1]
  simp only [valMat_gmm hω]

theorem mat_tvEl2 (hK : Nat.card K = (2 ^ 2) ^ 2) (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) :
    mat σ₄ (tvEl2 hK hω) = valMat ω (tvG ![0, 0, 1, 1]) := by
  simp only [tvEl2, mat_mul, mat_letterEl hK hω, mat_blockEl hK hω]
  rw [← check_tv2]
  simp only [valMat_gmm hω]

end Words

section Final

omit [Finite K] [CharP K 2] in
theorem four_roots {c c₁ c₂ : K} (h2 : (2 : K) = 0) (hs : c₁ + c₂ = 1) (hp : c₁ * c₂ = 1)
    (hc : c + c ^ 4 = 0) : c = 0 ∨ c = 1 ∨ c = c₁ ∨ c = c₂ := by
  have h : c * ((c + 1) * ((c + c₁) * (c + c₂))) = 0 := by
    linear_combination hc + (c ^ 2 * (c + 1)) * h2 + (c * (c + 1) * c) * hs + (c * (c + 1)) * hp
  rcases mul_eq_zero.mp h with h0 | h
  · exact Or.inl h0
  rcases mul_eq_zero.mp h with h1 | h
  · exact Or.inr (Or.inl (by linear_combination h1 - h2))
  rcases mul_eq_zero.mp h with h3 | h4
  · exact Or.inr (Or.inr (Or.inl (by linear_combination h3 - c₁ * h2)))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h4 - c₂ * h2)))

theorem val_norm_fixed (hω : ω ^ 4 + ω ^ 3 + ω ^ 2 + ω + 1 = 0) (a : G16) (ha : gconj a = a) :
    val ω a + σ₄ (val ω a) = 0 := by
  rw [← val_gconj hω σ₄ (sigma_omega ω) a, ha]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  linear_combination (val ω a) * h2

theorem eq_top_of_four (hK : Nat.card K = (2 ^ 2) ^ 2) (M : Subgroup (SUid σ₄ 5))
    (hD : ∀ (t : Fin 5 → K) (ht : ∀ i, σ₄ (t i) * t i = 1) (hdet : ∏ i, t i = 1),
      dgSU σ₄ t ht hdet ∈ M)
    (hC : ∀ g : SUid σ₄ 5,
      mat σ₄ g * U5Eigen.shiftMat = U5Eigen.shiftMat * mat σ₄ g → g ∈ M)
    (hS : ∀ x ∈ M, shiftSU σ₄ * x * (shiftSU σ₄)⁻¹ ∈ M) : M = ⊤ := by
  obtain ⟨ω, hω⟩ := exists_omega hK
  have h2 : (2 : K) = 0 := two_eq_zero
  have hσ : ∀ c : K, σ₄ (σ₄ c) = c := unitaryInvolution_involutive hK
  have hC' : ∀ g : SUid σ₄ 5, mat σ₄ g * valMat ω Sg = valMat ω Sg * mat σ₄ g → g ∈ M := by
    intro g hg
    rw [valMat_Sg] at hg
    exact hC g hg
  have hL : ∀ k, letterEl hK hω k ∈ M := letterEl_mem hK hω M hD hC'
  have ha₀ : herm σ₄ (![0, 0, 0, 1, 1] : Fin 5 → K) ![0, 0, 0, 1, 1] = 0 := by
    simp only [herm, Fin.sum_univ_five]
    simp
    linear_combination h2
  have hc₁ : val ω ![1, 0, 1, 1] + σ₄ (val ω ![1, 0, 1, 1]) = 0 :=
    val_norm_fixed hω _ (by decide +kernel)
  have hc₂ : val ω ![0, 0, 1, 1] + σ₄ (val ω ![0, 0, 1, 1]) = 0 :=
    val_norm_fixed hω _ (by decide +kernel)
  have hs : val ω ![1, 0, 1, 1] + val ω ![0, 0, 1, 1] = 1 := by
    have e : (![1, 0, 1, 1] + ![0, 0, 1, 1] : G16) = wpow 0 := by decide +kernel
    rw [← val_add, e, val_wpow hω]
    simp
  have hp : val ω ![1, 0, 1, 1] * val ω ![0, 0, 1, 1] = 1 := by
    have e : gmul ![1, 0, 1, 1] ![0, 0, 1, 1] = wpow 0 := by decide +kernel
    rw [← val_gmul hω, e, val_wpow hω]
    simp
  have mem_tv : ∀ (g : SUid σ₄ 5) (c : G16) (hc : val ω c + σ₄ (val ω c) = 0), g ∈ M →
      mat σ₄ g = valMat ω (tvG c) → tv hσ ha₀ hc ∈ M := by
    intro g c hc hg hmat
    have : tv hσ ha₀ hc = g := by
      apply Subtype.ext
      apply Units.ext
      show mat σ₄ (tv hσ ha₀ hc) = mat σ₄ g
      rw [hmat, valMat_tvG σ₄ (map_one σ₄) c]
      rfl
    rw [this]
    exact hg
  have ht₁ : tv hσ ha₀ hc₁ ∈ M :=
    mem_tv (tvEl1 hK hω) _ hc₁ (by
      refine M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem (hL 11) (hL 11)) ?_) (hL 3)) (hL 3)
      exact blockEl_mem hK hω M hL) (mat_tvEl1 hK hω)
  have ht₂ : tv hσ ha₀ hc₂ ∈ M :=
    mem_tv (tvEl2 hK hω) _ hc₂ (by
      have hB := blockEl_mem hK hω M hL
      exact M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem (hL 3) hB) (hL 3)) (hL 3)) hB)
      (mat_tvEl2 hK hω)
  have hu : (![0, 0, 0, 1, 1] : Fin 5 → K) ∈ Cset hσ M := by
    refine ⟨ha₀, fun c hc => ?_⟩
    have hc4 : c + c ^ 4 = 0 := by rwa [sigma_apply] at hc
    rcases four_roots h2 hs hp hc4 with rfl | rfl | rfl | rfl
    · rw [tv_zero hσ ha₀ hc]
      exact M.one_mem
    · have hcd : (val ω ![1, 0, 1, 1] + val ω ![0, 0, 1, 1]) +
          σ₄ (val ω ![1, 0, 1, 1] + val ω ![0, 0, 1, 1]) = 0 := by
        rw [hs, map_one]
        linear_combination h2
      rw [tv_congr σ₄ hσ ha₀ hs.symm hc hcd, ← tv_mul_tv hσ ha₀ hc₁ hc₂ hcd]
      exact M.mul_mem ht₁ ht₂
    · exact ht₁
    · exact ht₂
  have hDτ : ∀ (τ : K) (hτ : σ₄ τ * τ = 1), dgTau τ hτ ∈ M := fun τ hτ => hD _ _ _
  refine eq_top_of_ext3_shift hK (by norm_num) M (fun a ha => ?_) hS
  have e : extVec 3 a = ![0, 0, 0, a 0, a 1] := by
    ext k
    fin_cases k <;> simp [extVec_eq]
  rw [e]
  refine plane_all_of_point hσ h2 M hDτ one_ne_zero one_ne_zero rfl hu (a 0) (a 1) ?_
  simp only [herm, Fin.sum_univ_two] at ha
  linear_combination ha - (σ₄ (a 1) * a 1) * h2

end Final

end Group

end CFSG.RankThree.PartOne.CTP.U5Four
