module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerModel

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule

namespace TwE6Per

abbrev matS {k : Type} [Field k] (c : k) : Matrix (Fin 2) (Fin 2) k :=
  !![0, 1; -1, 0] * !![1, c; 0, 1]

section Matrix

variable {k : Type} [Field k]

theorem matS_ne_one (c : k) : matS c ≠ 1 := by
  intro h
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) k => M 0 0) h
  simp at this

variable [CharP k 2]

theorem mat_mul_P (a b : k) (hab : a * b = 1) :
    matS (a + b) * !![1, 1; a, b] = !![1, 1; a, b] * Matrix.diagonal ![a, b] := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]
  · linear_combination (-1 : k) * hab - (1 + a ^ 2) * h2
  · linear_combination (-1 : k) * hab - (1 + b ^ 2) * h2

theorem matS_pow (μ : kˣ) (hμ : μ * μ ≠ 1) {p : ℕ} (hp : μ ^ p = 1) :
    matS ((μ : k) + ((μ⁻¹ : kˣ) : k)) ^ p = 1 := by
  set a : k := (μ : k)
  set b : k := ((μ⁻¹ : kˣ) : k)
  have hab : a * b = 1 := Units.mul_inv μ
  set P : Matrix (Fin 2) (Fin 2) k := !![1, 1; a, b]
  set D : Matrix (Fin 2) (Fin 2) k := Matrix.diagonal ![a, b]
  have hMP := mat_mul_P a b hab
  have hpow : ∀ m : ℕ, matS (a + b) ^ m * P = P * D ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, mul_assoc, hMP, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have hD : D ^ p = 1 := by
    rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i
    · show a ^ p = 1
      rw [← Units.val_pow_eq_pow_val, hp, Units.val_one]
    · show b ^ p = 1
      rw [← Units.val_pow_eq_pow_val, inv_pow, hp, inv_one, Units.val_one]
  have hne : a ≠ b := by
    intro h
    apply hμ
    apply Units.ext
    rw [Units.val_mul, Units.val_one]
    have e : a * a = a * b := by rw [← h]
    exact e.trans hab
  have hdet : IsUnit P := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two]
    refine isUnit_iff_ne_zero.2 ?_
    simp only [P, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, one_mul]
    exact sub_ne_zero.2 (Ne.symm hne)
  have h1 : matS (a + b) ^ p * P = 1 * P := by rw [hpow p, hD, mul_one, one_mul]
  exact (hdet.mul_left_inj).1 h1

end Matrix


theorem not_isRoot_of_form' {γ : Fin (Tag.rank .E6) → ℤ} (h : MinData.toWeight γ ⬝ᵥ γ ≠ 2) :
    ¬ IsRoot .E6 γ :=
  fun hr => h (form_self_root posDef_cartan_E6 hr)

section Elt

variable {k : Type} [Field k]

@[expose] noncomputable def sElt (i : Fin (Tag.rank .E6)) (c : k) : e6Data_valid.minGroup k :=
  e6Data_valid.nm k i * e6Data_valid.xm k (Pi.single i 1) c

theorem sElt_mem_rankOne (i : Fin (Tag.rank .E6)) (c : k) :
    sElt i c ∈ rankOne k (Pi.single i 1) :=
  mul_mem (nm_mem_rankOne i) (xm_mem_rankOne _ c)

theorem endo_pow (g : e6Data_valid.minGroup k) (m : ℕ) :
    e6Data_valid.endo k (g ^ m) = e6Data_valid.endo k g ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, e6Data_valid.endo_mul, ih, pow_succ]

theorem endo_sElt (i : Fin (Tag.rank .E6)) (c : k) :
    e6Data_valid.endo k (sElt i c) = e6Data_valid.blockOp k i (matS c) := by
  rw [sElt, e6Data_valid.endo_mul, e6Data_valid.endo_nm, e6Data_valid.endo_xm,
    e6Data_valid.blockOp_mul, e6Data_valid.blockOp_weyl, e6Data_valid.blockOp_upper]

theorem sElt_ne_one (i : Fin (Tag.rank .E6)) (c : k) : sElt i c ≠ 1 := by
  intro h
  have h1 := congrArg (e6Data_valid.endo k) h
  rw [endo_sElt, e6Data_valid.endo_one, ← e6Data_valid.blockOp_one k i] at h1
  exact matS_ne_one c (e6Data_valid.blockOp_injective k i h1)

variable [CharP k 2]

theorem sElt_pow (i : Fin (Tag.rank .E6)) (μ : kˣ) (hμ : μ * μ ≠ 1) {p : ℕ} (hp : μ ^ p = 1) :
    sElt i ((μ : k) + ((μ⁻¹ : kˣ) : k)) ^ p = 1 := by
  apply e6Data_valid.endo_injective k
  have e : e6Data_valid.blockOp k i (matS ((μ : k) + ((μ⁻¹ : kˣ) : k))) ^ p =
      e6Data_valid.blockOp k i (matS ((μ : k) + ((μ⁻¹ : kˣ) : k)) ^ p) :=
    ((e6Data_valid.blockHom k i).map_pow _ p).symm
  rw [endo_pow, endo_sElt, e6Data_valid.endo_one, e, matS_pow μ hμ hp, e6Data_valid.blockOp_one]

theorem nm_inv_two (i : Fin (Tag.rank .E6)) :
    (e6Data_valid.nm k i)⁻¹ = e6Data_valid.nm k i :=
  inv_eq_of_mul_eq_one_left (nm_sq_two i)

theorem nm_conj_sElt (i : Fin (Tag.rank .E6)) (c : k) :
    e6Data_valid.nm k i * sElt i c * (e6Data_valid.nm k i)⁻¹ = (sElt i c)⁻¹ := by
  have hx : (e6Data_valid.xm k (Pi.single i 1) c)⁻¹ = e6Data_valid.xm k (Pi.single i 1) c :=
    inv_eq_of_mul_eq_one_left (xm_mul_self_two _ c)
  rw [sElt, mul_inv_rev, hx, nm_inv_two, ← mul_assoc, nm_sq_two, one_mul]

end Elt

end TwE6Per

end CFSG.StandardType
