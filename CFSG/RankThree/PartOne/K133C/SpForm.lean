module

public import CFSG.RankThree.PartOne.K133C.FlagRadical

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix

set_option linter.unusedSectionVars false

section Form

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (J : Matrix ι ι K)

@[expose] def bf (y z : ι → K) : K := y ⬝ᵥ (J *ᵥ z)

theorem bf_add_left (x y z : ι → K) : bf J (x + y) z = bf J x z + bf J y z := by
  simp [bf, add_dotProduct]

theorem bf_add_right (x y z : ι → K) : bf J x (y + z) = bf J x y + bf J x z := by
  simp [bf, mulVec_add, dotProduct_add]

theorem bf_smul_left (c : K) (x y : ι → K) : bf J (c • x) y = c * bf J x y := by
  simp [bf, smul_dotProduct]

theorem bf_smul_right (c : K) (x y : ι → K) : bf J x (c • y) = c * bf J x y := by
  simp [bf, mulVec_smul, dotProduct_smul]

theorem bf_zero_right (y : ι → K) : bf J y 0 = 0 := by simp [bf]

theorem bf_comm (hJ : Jᵀ = J) (y z : ι → K) : bf J y z = bf J z y := by
  unfold bf
  rw [dotProduct_mulVec, ← mulVec_transpose, hJ, dotProduct_comm]

@[expose] def isoGrp : Subgroup (GL ι K) where
  carrier := {g | (g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K) = J}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    change (a : Matrix ι ι K)ᵀ * J * (a : Matrix ι ι K) = J at ha
    change (b : Matrix ι ι K)ᵀ * J * (b : Matrix ι ι K) = J at hb
    change ((a * b : GL ι K) : Matrix ι ι K)ᵀ * J * ((a * b : GL ι K) : Matrix ι ι K) = J
    rw [Units.val_mul, transpose_mul]
    calc (b : Matrix ι ι K)ᵀ * (a : Matrix ι ι K)ᵀ * J * ((a : Matrix ι ι K) * (b : Matrix ι ι K))
        = (b : Matrix ι ι K)ᵀ * ((a : Matrix ι ι K)ᵀ * J * (a : Matrix ι ι K)) * (b : Matrix ι ι K) := by
          simp only [mul_assoc]
      _ = J := by rw [ha, hb]
  inv_mem' := fun {g} hg => by
    change (g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K) = J at hg
    change ((g⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * J * ((g⁻¹ : GL ι K) : Matrix ι ι K) = J
    have h1 : (g : Matrix ι ι K) * ((g⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((g⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * J * ((g⁻¹ : GL ι K) : Matrix ι ι K)
        = ((g⁻¹ : GL ι K) : Matrix ι ι K)ᵀ * ((g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K)) *
            ((g⁻¹ : GL ι K) : Matrix ι ι K) := by rw [hg]
      _ = ((g : Matrix ι ι K) * ((g⁻¹ : GL ι K) : Matrix ι ι K))ᵀ * J *
            ((g : Matrix ι ι K) * ((g⁻¹ : GL ι K) : Matrix ι ι K)) := by
          simp only [transpose_mul, mul_assoc]
      _ = J := by rw [h1]; simp

theorem pairing_transpose (A : Matrix ι ι K) (v w : ι → K) :
    (A *ᵥ v) ⬝ᵥ (J *ᵥ (A *ᵥ w)) = v ⬝ᵥ ((Aᵀ * J * A) *ᵥ w) := by
  calc (A *ᵥ v) ⬝ᵥ (J *ᵥ (A *ᵥ w)) = v ⬝ᵥ (Aᵀ *ᵥ (J *ᵥ (A *ᵥ w))) := by
        rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
    _ = v ⬝ᵥ ((Aᵀ * J * A) *ᵥ w) := by rw [mulVec_mulVec, mulVec_mulVec, mul_assoc]

theorem transpose_mul_eq_of_pairing {A : Matrix ι ι K}
    (h : ∀ v w : ι → K, (A *ᵥ v) ⬝ᵥ (J *ᵥ (A *ᵥ w)) = v ⬝ᵥ (J *ᵥ w)) : Aᵀ * J * A = J := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [pairing_transpose] at this
  simpa using this

theorem mem_isoGrp_iff {g : GL ι K} :
    g ∈ isoGrp J ↔ ∀ y z : ι → K, bf J ((g : Matrix ι ι K) *ᵥ y) ((g : Matrix ι ι K) *ᵥ z) = bf J y z := by
  constructor
  · intro hg y z
    have h : (g : Matrix ι ι K)ᵀ * J * (g : Matrix ι ι K) = J := hg
    unfold bf
    rw [pairing_transpose, h]
  · intro h
    exact transpose_mul_eq_of_pairing J (fun v w => h v w)

theorem vecMulVec_mulVec' (u a y : ι → K) : vecMulVec u a *ᵥ y = (a ⬝ᵥ y) • u := by
  rw [vecMulVec_mulVec, op_smul_eq_smul]

@[expose] def trvM (v : ι → K) (a : K) : Matrix ι ι K := 1 + a • vecMulVec v (J *ᵥ v)

theorem trvM_mulVec (v : ι → K) (a : K) (y : ι → K) :
    trvM J v a *ᵥ y = y + (a * bf J y v) • v := by
  rw [trvM, add_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec', smul_smul, bf, dotProduct_comm]

@[expose] def sglM (v w : ι → K) : Matrix ι ι K :=
  1 + vecMulVec w (J *ᵥ v) + vecMulVec v (J *ᵥ w)

theorem sglM_mulVec (v w y : ι → K) :
    sglM J v w *ᵥ y = y + bf J y v • w + bf J y w • v := by
  rw [sglM, add_mulVec, add_mulVec, one_mulVec, vecMulVec_mulVec', vecMulVec_mulVec', bf, bf,
    dotProduct_comm (J *ᵥ v), dotProduct_comm (J *ᵥ w)]

theorem trvM_mul_self [CharP K 2] (hJa : ∀ y, y ⬝ᵥ (J *ᵥ y) = 0) (v : ι → K) (a : K) :
    trvM J v a * trvM J v a = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hvv : bf J v v = 0 := hJa v
  rw [Matrix.ext_iff_mulVec]
  intro y
  rw [← mulVec_mulVec, one_mulVec, trvM_mulVec, trvM_mulVec, bf_add_left, bf_smul_left, hvv]
  have : y + (a * bf J y v) • v + (a * (bf J y v + (a * bf J y v) * 0)) • v =
      y + (2 : K) • ((a * bf J y v) • v) := by
    rw [two_smul, mul_zero, add_zero]
    abel
  rw [this, h2, zero_smul, add_zero]

theorem trvM_isometry [CharP K 2] (hJ : Jᵀ = J) (hJa : ∀ y, y ⬝ᵥ (J *ᵥ y) = 0) (v : ι → K) (a : K)
    (y z : ι → K) : bf J (trvM J v a *ᵥ y) (trvM J v a *ᵥ z) = bf J y z := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hvv : bf J v v = 0 := hJa v
  rw [trvM_mulVec, trvM_mulVec]
  simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, hvv, bf_comm J hJ v z]
  linear_combination (a * bf J y v * bf J z v) * h2

theorem sglM_mul_self [CharP K 2] (hJ : Jᵀ = J) (hJa : ∀ y, y ⬝ᵥ (J *ᵥ y) = 0) {v w : ι → K}
    (hvw : bf J v w = 0) : sglM J v w * sglM J v w = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hvv : bf J v v = 0 := hJa v
  have hww : bf J w w = 0 := hJa w
  have hwv : bf J w v = 0 := by rw [bf_comm J hJ]; exact hvw
  rw [Matrix.ext_iff_mulVec]
  intro y
  have key : ∀ m : ι → K, m + m = 0 := fun m => by rw [← two_smul K m, h2, zero_smul]
  rw [← mulVec_mulVec, one_mulVec, sglM_mulVec, sglM_mulVec]
  simp only [bf_add_left, bf_smul_left, hvv, hww, hvw, hwv, mul_zero, add_zero]
  calc _ = y + (bf J y v • w + bf J y v • w) + (bf J y w • v + bf J y w • v) := by abel
    _ = y := by rw [key, key, add_zero, add_zero]

theorem sglM_isometry [CharP K 2] (hJ : Jᵀ = J) (hJa : ∀ y, y ⬝ᵥ (J *ᵥ y) = 0) {v w : ι → K}
    (hvw : bf J v w = 0) (y z : ι → K) :
    bf J (sglM J v w *ᵥ y) (sglM J v w *ᵥ z) = bf J y z := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hvv : bf J v v = 0 := hJa v
  have hww : bf J w w = 0 := hJa w
  have hwv : bf J w v = 0 := by rw [bf_comm J hJ]; exact hvw
  rw [sglM_mulVec, sglM_mulVec]
  simp only [bf_add_left, bf_add_right, bf_smul_left, bf_smul_right, hvv, hww, hvw, hwv,
    bf_comm J hJ w z, bf_comm J hJ v z]
  linear_combination (bf J y w * bf J z v + bf J y v * bf J z w) * h2

theorem mulVec_inv_mulVec (h : GL ι K) (y : ι → K) :
    (h : Matrix ι ι K) *ᵥ (((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) = y := by
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem exists_bf_ne_zero (hJnd : ∀ w : ι → K, J *ᵥ w = 0 → w = 0) {v : ι → K} (hv : v ≠ 0) :
    ∃ y : ι → K, bf J y v ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  apply hJnd
  funext i
  have := h (Pi.single i 1)
  simpa [bf] using this

theorem trvM_mul (hJa : ∀ y, y ⬝ᵥ (J *ᵥ y) = 0) (v : ι → K) (a b : K) :
    trvM J v a * trvM J v b = trvM J v (a + b) := by
  have hvv : bf J v v = 0 := hJa v
  rw [Matrix.ext_iff_mulVec]
  intro y
  rw [← mulVec_mulVec, trvM_mulVec, trvM_mulVec, trvM_mulVec, bf_add_left, bf_smul_left, hvv]
  simp only [mul_zero, add_zero]
  rw [add_assoc, ← add_smul, show b * bf J y v + a * bf J y v = (a + b) * bf J y v by ring]

theorem trvM_inj [CharP K 2] (hJnd : ∀ w : ι → K, J *ᵥ w = 0 → w = 0) {v : ι → K} (hv : v ≠ 0) {a b : K}
    (h : ∀ y, trvM J v a *ᵥ y = trvM J v b *ᵥ y) : a = b := by
  obtain ⟨y₀, hy₀⟩ := exists_bf_ne_zero J hJnd hv
  have h1 := h y₀
  rw [trvM_mulVec, trvM_mulVec] at h1
  have h2 : (a * bf J y₀ v) • v = (b * bf J y₀ v) • v := add_left_cancel h1
  have h3 : a * bf J y₀ v = b * bf J y₀ v := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hno
      push Not at hno
      exact hv (funext hno)
    have := congrFun h2 i
    simpa [hi] using this
  exact mul_right_cancel₀ hy₀ h3

theorem sglM_inj [CharP K 2] (hJnd : ∀ w : ι → K, J *ᵥ w = 0 → w = 0) {v w w' : ι → K} (hv : v ≠ 0)
    (h : ∀ y, sglM J v w *ᵥ y = sglM J v w' *ᵥ y) : ∃ c : K, w' - w = c • v := by
  obtain ⟨y₀, hy₀⟩ := exists_bf_ne_zero J hJnd hv
  set b := bf J y₀ v with hb
  have h1 := h y₀
  rw [sglM_mulVec, sglM_mulVec] at h1
  have h3 : (y₀ + b • w' + bf J y₀ w' • v) - (y₀ + b • w + bf J y₀ w • v) = 0 :=
    sub_eq_zero.2 h1.symm
  have h4 : b • (w' - w) = (bf J y₀ w - bf J y₀ w') • v := by
    rw [smul_sub, sub_smul]
    calc b • w' - b • w = ((y₀ + b • w' + bf J y₀ w' • v) - (y₀ + b • w + bf J y₀ w • v)) +
          (bf J y₀ w • v - bf J y₀ w' • v) := by abel
      _ = bf J y₀ w • v - bf J y₀ w' • v := by rw [h3, zero_add]
  refine ⟨b⁻¹ * (bf J y₀ w - bf J y₀ w'), ?_⟩
  apply smul_right_injective (ι → K) hy₀
  show b • (w' - w) = b • ((b⁻¹ * (bf J y₀ w - bf J y₀ w')) • v)
  rw [h4, smul_smul, ← mul_assoc, mul_inv_cancel₀ hy₀, one_mul]

section GLValued

variable [CharP K 2] (hJa : ∀ y : ι → K, y ⬝ᵥ (J *ᵥ y) = 0)

@[expose] def trvGL (v : ι → K) (a : K) : GL ι K :=
  ⟨trvM J v a, trvM J v a, trvM_mul_self J hJa v a, trvM_mul_self J hJa v a⟩

theorem coe_trvGL (v : ι → K) (a : K) :
    ((trvGL J hJa v a : GL ι K) : Matrix ι ι K) = trvM J v a := rfl

theorem trvGL_zero (v : ι → K) : trvGL J hJa v 0 = 1 := by
  apply Units.ext
  simp [coe_trvGL, trvM]

theorem trvGL_add (v : ι → K) (a b : K) :
    trvGL J hJa v (a + b) = trvGL J hJa v a * trvGL J hJa v b := by
  apply Units.ext
  rw [Units.val_mul, coe_trvGL, coe_trvGL, coe_trvGL, trvM_mul J hJa]

theorem trvGL_mem_isoGrp (hJ : Jᵀ = J) (v : ι → K) (a : K) : trvGL J hJa v a ∈ isoGrp J :=
  (mem_isoGrp_iff J).2 fun y z => trvM_isometry J hJ hJa v a y z

theorem trvGL_sq (v : ι → K) (a : K) : trvGL J hJa v a * trvGL J hJa v a = 1 := by
  rw [← trvGL_add, CharTwo.add_self_eq_zero, trvGL_zero]

theorem trvGL_inj (hJnd : ∀ w : ι → K, J *ᵥ w = 0 → w = 0) {v : ι → K} (hv : v ≠ 0) {a b : K}
    (h : trvGL J hJa v a = trvGL J hJa v b) : a = b :=
  trvM_inj J hJnd hv fun y => by
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) *ᵥ y) h
    exact this

theorem conj_trvGL {h : GL ι K} (hh : h ∈ isoGrp J) (v : ι → K) (a : K) :
    h * trvGL J hJa v a * h⁻¹ = trvGL J hJa ((h : Matrix ι ι K) *ᵥ v) a := by
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro y
  have hiso := (mem_isoGrp_iff J).1 hh (((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) v
  rw [mulVec_inv_mulVec] at hiso
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, coe_trvGL J hJa v a,
    trvM_mulVec J v a, mulVec_add, mulVec_smul, mulVec_inv_mulVec,
    coe_trvGL J hJa ((h : Matrix ι ι K) *ᵥ v) a, trvM_mulVec J ((h : Matrix ι ι K) *ᵥ v) a y, ← hiso]

end GLValued

section GLValuedSgl

variable [CharP K 2] (hJ : Jᵀ = J) (hJa : ∀ y : ι → K, y ⬝ᵥ (J *ᵥ y) = 0)

open _root_.Classical in
@[expose] noncomputable def sglGL (v w : ι → K) : GL ι K :=
  if hvw : bf J v w = 0 then
    ⟨sglM J v w, sglM J v w, sglM_mul_self J hJ hJa hvw, sglM_mul_self J hJ hJa hvw⟩
  else 1

theorem coe_sglGL {v w : ι → K} (hvw : bf J v w = 0) :
    ((sglGL J hJ hJa v w : GL ι K) : Matrix ι ι K) = sglM J v w := by
  rw [sglGL, dite_eq_left hvw]

theorem sglGL_mem_isoGrp {v w : ι → K} (hvw : bf J v w = 0) : sglGL J hJ hJa v w ∈ isoGrp J :=
  (mem_isoGrp_iff J).2 fun y z => by
    rw [coe_sglGL J hJ hJa hvw]
    exact sglM_isometry J hJ hJa hvw y z

theorem conj_sglGL {h : GL ι K} (hh : h ∈ isoGrp J) {v w : ι → K} (hvw : bf J v w = 0) :
    h * sglGL J hJ hJa v w * h⁻¹ = sglGL J hJ hJa ((h : Matrix ι ι K) *ᵥ v) ((h : Matrix ι ι K) *ᵥ w) := by
  have hiso := (mem_isoGrp_iff J).1 hh
  have hvw' : bf J ((h : Matrix ι ι K) *ᵥ v) ((h : Matrix ι ι K) *ᵥ w) = 0 := by
    rw [hiso]; exact hvw
  apply Units.ext
  rw [Matrix.ext_iff_mulVec]
  intro y
  have h1 := hiso (((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) v
  have h2 := hiso (((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ y) w
  rw [mulVec_inv_mulVec] at h1 h2
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, coe_sglGL J hJ hJa hvw,
    sglM_mulVec, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_inv_mulVec, ← h1, ← h2,
    coe_sglGL J hJ hJa hvw', sglM_mulVec]

theorem sglGL_inj (hJnd : ∀ w : ι → K, J *ᵥ w = 0 → w = 0) {v w w' : ι → K} (hv : v ≠ 0)
    (hvw : bf J v w = 0) (hvw' : bf J v w' = 0)
    (h : sglGL J hJ hJa v w = sglGL J hJ hJa v w') : ∃ c : K, w' - w = c • v :=
  sglM_inj J hJnd hv fun y => by
    have := congrArg (fun g : GL ι K => (g : Matrix ι ι K) *ᵥ y) h
    simpa only [coe_sglGL J hJ hJa hvw, coe_sglGL J hJ hJa hvw'] using this

theorem sglGL_mem_radFlag {v w : ι → K} (hvw : bf J v w = 0)
    (hψv : (J *ᵥ v) ⬝ᵥ v = 0) : sglGL J hJ hJa v w ∈ radFlag v (J *ᵥ v) hψv := by
  have hvv : bf J v v = 0 := hJa v
  have hww : bf J w w = 0 := hJa w
  have hwv : bf J w v = 0 := by rw [bf_comm J hJ]; exact hvw
  rw [mem_radFlag, coe_sglGL J hJ hJa hvw]
  have hψ : ∀ y, (J *ᵥ v) ⬝ᵥ y = bf J y v := fun y => dotProduct_comm _ _
  refine ⟨?_, fun y => ?_, fun y hy => ?_⟩
  · rw [sglM_mulVec, hvv, hvw]
    simp
  · rw [sglM_mulVec]
    have e : y + bf J y v • w + bf J y w • v - y = bf J y v • w + bf J y w • v := by abel
    rw [e, dotProduct_add, dotProduct_smul, dotProduct_smul, hψ w, hψ v, hwv, hvv]
    simp
  · refine ⟨bf J y w, ?_⟩
    rw [hψ] at hy
    rw [sglM_mulVec, hy]
    simp

end GLValuedSgl

end Form

end CFSG.RankThree.PartOne.K133C
