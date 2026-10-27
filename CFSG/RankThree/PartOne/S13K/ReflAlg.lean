module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K.ReflAlg

open Matrix

variable {p : ℕ} [Fact p.Prime]

@[expose] def IsRoot (α : Fin 3 → ZMod p) : Prop :=
  α = ![1, 0, 0] ∨ α = ![0, 1, 0] ∨ α = ![0, 0, 1] ∨ α = ![1, 1, 0] ∨ α = ![1, -1, 0] ∨
    α = ![0, 1, 1] ∨ α = ![0, 1, -1] ∨ α = ![1, 0, 1] ∨ α = ![1, 0, -1]

@[expose] noncomputable def reflMat (α : Fin 3 → ZMod p) : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  1 - ((2 : ZMod p) / (α ⬝ᵥ α)) • Matrix.vecMulVec α α

theorem reflMat_apply (α : Fin 3 → ZMod p) (i j : Fin 3) :
    reflMat α i j = (if i = j then 1 else 0) - ((2 : ZMod p) / (α ⬝ᵥ α)) * (α i * α j) := by
  simp [reflMat, Matrix.vecMulVec_apply, Matrix.one_apply]

theorem two_ne_zero_of_five_le (hp5 : 5 ≤ p) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have := (ZMod.natCast_eq_zero_iff 2 p).1 h'
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem dot_root_ne_zero (hp5 : 5 ≤ p) {α : Fin 3 → ZMod p} (hα : IsRoot α) : α ⬝ᵥ α ≠ 0 := by
  have h2 := two_ne_zero_of_five_le (p := p) hp5
  have h11 : (1 : ZMod p) + 1 ≠ 0 := by rw [one_add_one_eq_two]; exact h2
  rcases hα with h | h | h | h | h | h | h | h | h <;>
    simp [h, dotProduct, Fin.sum_univ_three, h11]

theorem exists_zero_root {α : Fin 3 → ZMod p} (hα : IsRoot α) : ∃ i, α i = 0 := by
  rcases hα with h | h | h | h | h | h | h | h | h
  · exact ⟨1, by simp [h]⟩
  · exact ⟨0, by simp [h]⟩
  · exact ⟨0, by simp [h]⟩
  · exact ⟨2, by simp [h]⟩
  · exact ⟨2, by simp [h]⟩
  · exact ⟨0, by simp [h]⟩
  · exact ⟨0, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩
  · exact ⟨1, by simp [h]⟩

theorem ne_zero_root {α : Fin 3 → ZMod p} (hα : IsRoot α) : α ≠ 0 := by
  intro h0
  have key : ∀ i, α i = 0 := fun i => by rw [h0]; rfl
  rcases hα with h | h | h | h | h | h | h | h | h
  · have := key 0; simp [h] at this
  · have := key 1; simp [h] at this
  · have := key 2; simp [h] at this
  · have := key 0; simp [h] at this
  · have := key 0; simp [h] at this
  · have := key 1; simp [h] at this
  · have := key 1; simp [h] at this
  · have := key 0; simp [h] at this
  · have := key 0; simp [h] at this

theorem conj_formula (M : Matrix (Fin 3) (Fin 3) (ZMod p)) (hM : M * M = 1) (α : Fin 3 → ZMod p) :
    M * reflMat α * M =
      1 - ((2 : ZMod p) / (α ⬝ᵥ α)) • Matrix.vecMulVec (M *ᵥ α) (Mᵀ *ᵥ α) := by
  unfold reflMat
  have h1 : M * Matrix.vecMulVec α α * M = Matrix.vecMulVec (M *ᵥ α) (Mᵀ *ᵥ α) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul,
    Matrix.smul_mul, hM, h1]

theorem key_root (hp5 : 5 ≤ p) (M : Matrix (Fin 3) (Fin 3) (ZMod p)) (hM : M * M = 1)
    {α β : Fin 3 → ZMod p} (hα : IsRoot α) (hβ : IsRoot β)
    (h : M * reflMat α = reflMat β * M) :
    (∃ κ : ZMod p, Mᵀ *ᵥ α = κ • (M *ᵥ α)) ∧ ∃ i, (M *ᵥ α) i = 0 := by
  have hcα : (2 : ZMod p) / (α ⬝ᵥ α) ≠ 0 :=
    div_ne_zero (two_ne_zero_of_five_le hp5) (dot_root_ne_zero hp5 hα)
  have h1 : M * reflMat α * M = reflMat β := by
    rw [h, Matrix.mul_assoc, hM, Matrix.mul_one]
  rw [conj_formula M hM α] at h1
  have h2 : ((2 : ZMod p) / (α ⬝ᵥ α)) • Matrix.vecMulVec (M *ᵥ α) (Mᵀ *ᵥ α) =
      ((2 : ZMod p) / (β ⬝ᵥ β)) • Matrix.vecMulVec β β := by
    unfold reflMat at h1
    exact sub_right_injective h1
  have hE : ∀ i j, ((2 : ZMod p) / (α ⬝ᵥ α)) * ((M *ᵥ α) i * (Mᵀ *ᵥ α) j) =
      ((2 : ZMod p) / (β ⬝ᵥ β)) * (β i * β j) := by
    intro i j
    have := congrFun (congrFun h2 i) j
    simpa [Matrix.vecMulVec_apply] using this
  have hMα : M *ᵥ α ≠ 0 := by
    intro h0
    apply ne_zero_root hα
    calc α = (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ α := (Matrix.one_mulVec α).symm
      _ = (M * M) *ᵥ α := by rw [hM]
      _ = M *ᵥ (M *ᵥ α) := (Matrix.mulVec_mulVec α M M).symm
      _ = 0 := by rw [h0, Matrix.mulVec_zero]
  have hMt : Mᵀ * Mᵀ = 1 := by
    rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]
  have hMtα : Mᵀ *ᵥ α ≠ 0 := by
    intro h0
    apply ne_zero_root hα
    calc α = (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ α := (Matrix.one_mulVec α).symm
      _ = (Mᵀ * Mᵀ) *ᵥ α := by rw [hMt]
      _ = Mᵀ *ᵥ (Mᵀ *ᵥ α) := (Matrix.mulVec_mulVec α Mᵀ Mᵀ).symm
      _ = 0 := by rw [h0, Matrix.mulVec_zero]
  refine ⟨?_, ?_⟩
  · obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hMα
    have hj₀' : (M *ᵥ α) j₀ ≠ 0 := hj₀
    refine ⟨(Mᵀ *ᵥ α) j₀ / (M *ᵥ α) j₀, ?_⟩
    funext i
    have hR : (M *ᵥ α) j₀ * (Mᵀ *ᵥ α) i = (M *ᵥ α) i * (Mᵀ *ᵥ α) j₀ := by
      apply mul_left_cancel₀ hcα
      calc ((2 : ZMod p) / (α ⬝ᵥ α)) * ((M *ᵥ α) j₀ * (Mᵀ *ᵥ α) i)
          = ((2 : ZMod p) / (β ⬝ᵥ β)) * (β j₀ * β i) := hE j₀ i
        _ = ((2 : ZMod p) / (β ⬝ᵥ β)) * (β i * β j₀) := by rw [mul_comm (β j₀)]
        _ = ((2 : ZMod p) / (α ⬝ᵥ α)) * ((M *ᵥ α) i * (Mᵀ *ᵥ α) j₀) := (hE i j₀).symm
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination hR
  · obtain ⟨j₁, hj₁⟩ := Function.ne_iff.mp hMtα
    have hj₁' : (Mᵀ *ᵥ α) j₁ ≠ 0 := hj₁
    obtain ⟨i₀, hi₀⟩ := exists_zero_root hβ
    refine ⟨i₀, ?_⟩
    have := hE i₀ j₁
    rw [hi₀, zero_mul, mul_zero] at this
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hcα
    · rcases mul_eq_zero.mp h0 with h0 | h0
      · exact h0
      · exact absurd h0 hj₁'

theorem scalar_of_roots (N : Matrix (Fin 3) (Fin 3) (ZMod p))
    (h : ∀ α : Fin 3 → ZMod p, IsRoot α → ∃ κ : ZMod p, N *ᵥ α = κ • α) :
    ∃ κ : ZMod p, N = κ • (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
  obtain ⟨k0, h0⟩ := h ![1, 0, 0] (Or.inl rfl)
  obtain ⟨k1, h1⟩ := h ![0, 1, 0] (Or.inr (Or.inl rfl))
  obtain ⟨k2, h2⟩ := h ![0, 0, 1] (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨k01, h01⟩ := h ![1, 1, 0] (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨k12, h12⟩ := h ![0, 1, 1] (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have a00 := congrFun h0 0
  have a10 := congrFun h0 1
  have a20 := congrFun h0 2
  have a01 := congrFun h1 0
  have a11 := congrFun h1 1
  have a21 := congrFun h1 2
  have a02 := congrFun h2 0
  have a12 := congrFun h2 1
  have a22 := congrFun h2 2
  have b0 := congrFun h01 0
  have b1 := congrFun h01 1
  have c1 := congrFun h12 1
  have c2 := congrFun h12 2
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three] at a00 a10 a20 a01 a11 a21 a02 a12 a22 b0 b1 c1 c2
  have d11 : N 1 1 = N 0 0 := by linear_combination b1 - b0 - a10 + a01
  have d22 : N 2 2 = N 0 0 := by linear_combination c2 - c1 - a21 + a12 + d11
  refine ⟨N 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a10, a20, a01, a21, a02, a12, d11, d22]

theorem dot_eq_neg_two {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hM2 : M * M = 1)
    {u φ : Fin 3 → ZMod p} (hu : u ≠ 0) (hφ : φ ≠ 0) (hM : M = 1 + Matrix.vecMulVec u φ) :
    φ ⬝ᵥ u = -2 := by
  have hV : (1 + Matrix.vecMulVec u φ) * (1 + Matrix.vecMulVec u φ) =
      1 + ((2 : ZMod p) + φ ⬝ᵥ u) • Matrix.vecMulVec u φ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.add_apply, Matrix.one_apply,
      dotProduct, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [hM, hV] at hM2
  have h0 : ((2 : ZMod p) + φ ⬝ᵥ u) • Matrix.vecMulVec u φ = 0 := by
    have := congrArg (fun A => A - 1) hM2
    simpa using this
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hu
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hφ
  have h1 := congrFun (congrFun h0 i₀) j₀
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, Matrix.zero_apply] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · linear_combination h2
  · rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hi₀
    · exact absurd h3 hj₀

theorem zero_cases {c a b e x y z : ZMod p}
    (h : ∃ i : Fin 3, (![x, y, z] : Fin 3 → ZMod p) i +
      c * ((![a, b, e] : Fin 3 → ZMod p) i * ((![a, b, e] : Fin 3 → ZMod p) ⬝ᵥ ![x, y, z])) = 0) :
    x + c * (a * (a * x + b * y + e * z)) = 0 ∨ y + c * (b * (a * x + b * y + e * z)) = 0 ∨
      z + c * (e * (a * x + b * y + e * z)) = 0 := by
  have hs : (![a, b, e] : Fin 3 → ZMod p) ⬝ᵥ ![x, y, z] = a * x + b * y + e * z := by
    simp [dotProduct, Fin.sum_univ_three]
  obtain ⟨i, hi⟩ := h
  rw [hs] at hi
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)

theorem root_of_zero (hp5 : 5 ≤ p) {u : Fin 3 → ZMod p} (hu : u ≠ 0) {c : ZMod p}
    (hc : c * (u ⬝ᵥ u) = -2)
    (hzero : ∀ α : Fin 3 → ZMod p, IsRoot α → ∃ i, α i + c * (u i * (u ⬝ᵥ α)) = 0) :
    ∃ (t : ZMod p) (β : Fin 3 → ZMod p), IsRoot β ∧ t ≠ 0 ∧ u = t • β := by
  have h2 := two_ne_zero_of_five_le (p := p) hp5
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h2
    linear_combination hc
  obtain ⟨a, b, e, rfl⟩ : ∃ a b e : ZMod p, u = ![a, b, e] :=
    ⟨u 0, u 1, u 2, by funext i; fin_cases i <;> rfl⟩
  have hn : (![a, b, e] : Fin 3 → ZMod p) ⬝ᵥ ![a, b, e] = a * a + b * b + e * e := by
    simp [dotProduct, Fin.sum_univ_three]
  rw [hn] at hc
  have D0 := zero_cases (hzero ![1, 0, 0] (Or.inl rfl))
  have D1 := zero_cases (hzero ![0, 1, 0] (Or.inr (Or.inl rfl)))
  have D2 := zero_cases (hzero ![0, 0, 1] (Or.inr (Or.inr (Or.inl rfl))))
  have D01 := zero_cases (hzero ![1, 1, 0] (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have D02 := zero_cases (hzero ![1, 0, 1]
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
  have nz : ∀ x y : ZMod p, x ≠ 0 → y ≠ 0 → c * (x * y) ≠ 0 := fun x y hx hy =>
    mul_ne_zero hc0 (mul_ne_zero hx hy)
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases he : e = 0
  · exact absurd (by funext i; fin_cases i <;> simp [ha, hb, he]) hu
  · refine ⟨e, ![0, 0, 1], Or.inr (Or.inr (Or.inl rfl)), he, ?_⟩
    funext i; fin_cases i <;> simp [ha, hb]
  · refine ⟨b, ![0, 1, 0], Or.inr (Or.inl rfl), hb, ?_⟩
    funext i; fin_cases i <;> simp [ha, he]
  ·
    subst ha
    have hcb : c * (b * b) = -1 := by
      rcases D01 with h | h | h
      · exact absurd (by linear_combination h : (1 : ZMod p) = 0) one_ne_zero
      · linear_combination h
      · exact absurd (by linear_combination h : c * (e * b) = 0) (nz e b he hb)
    have hbe : e * e = b * b := by
      apply mul_left_cancel₀ hc0
      linear_combination hc - 2 * hcb
    rcases mul_self_eq_mul_self_iff.mp hbe with h | h
    · exact ⟨b, ![0, 1, 1], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), hb, by
        funext i; fin_cases i <;> simp [h]⟩
    · exact ⟨b, ![0, 1, -1], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), hb, by
        funext i; fin_cases i <;> simp [h]⟩
  · refine ⟨a, ![1, 0, 0], Or.inl rfl, ha, ?_⟩
    funext i; fin_cases i <;> simp [hb, he]
  ·
    subst hb
    have hca : c * (a * a) = -1 := by
      rcases D01 with h | h | h
      · linear_combination h
      · exact absurd (by linear_combination h : (1 : ZMod p) = 0) one_ne_zero
      · exact absurd (by linear_combination h : c * (e * a) = 0) (nz e a he ha)
    have hae : e * e = a * a := by
      apply mul_left_cancel₀ hc0
      linear_combination hc - 2 * hca
    rcases mul_self_eq_mul_self_iff.mp hae with h | h
    · exact ⟨a, ![1, 0, 1], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))), ha, by
        funext i; fin_cases i <;> simp [h]⟩
    · exact ⟨a, ![1, 0, -1], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))), ha, by
        funext i; fin_cases i <;> simp [h]⟩
  ·
    subst he
    have hca : c * (a * a) = -1 := by
      rcases D02 with h | h | h
      · linear_combination h
      · exact absurd (by linear_combination h : c * (b * a) = 0) (nz b a hb ha)
      · exact absurd (by linear_combination h : (1 : ZMod p) = 0) one_ne_zero
    have hab : b * b = a * a := by
      apply mul_left_cancel₀ hc0
      linear_combination hc - 2 * hca
    rcases mul_self_eq_mul_self_iff.mp hab with h | h
    · exact ⟨a, ![1, 1, 0], Or.inr (Or.inr (Or.inr (Or.inl rfl))), ha, by
        funext i; fin_cases i <;> simp [h]⟩
    · exact ⟨a, ![1, -1, 0], Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), ha, by
        funext i; fin_cases i <;> simp [h]⟩
  ·
    exfalso
    have k0 : 1 + c * (a * a) = 0 := by
      rcases D0 with h | h | h
      · linear_combination h
      · exact absurd (by linear_combination h : c * (b * a) = 0) (nz b a hb ha)
      · exact absurd (by linear_combination h : c * (e * a) = 0) (nz e a he ha)
    have k1 : 1 + c * (b * b) = 0 := by
      rcases D1 with h | h | h
      · exact absurd (by linear_combination h : c * (a * b) = 0) (nz a b ha hb)
      · linear_combination h
      · exact absurd (by linear_combination h : c * (e * b) = 0) (nz e b he hb)
    have k2 : 1 + c * (e * e) = 0 := by
      rcases D2 with h | h | h
      · exact absurd (by linear_combination h : c * (a * e) = 0) (nz a e ha he)
      · exact absurd (by linear_combination h : c * (b * e) = 0) (nz b e hb he)
      · linear_combination h
    exact one_ne_zero (by linear_combination k0 + k1 + k2 - hc : (1 : ZMod p) = 0)

theorem refl_of_smul (hp5 : 5 ≤ p) {u β : Fin 3 → ZMod p} {t c : ZMod p} (hβ : IsRoot β)
    (hu : u = t • β) (hc : c * (u ⬝ᵥ u) = -2) :
    (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) + c • Matrix.vecMulVec u u = reflMat β := by
  have hB := dot_root_ne_zero hp5 hβ
  subst hu
  have hdot : (t • β) ⬝ᵥ (t • β) = t * (t * (β ⬝ᵥ β)) := by
    simp [smul_dotProduct, dotProduct_smul]
  rw [hdot] at hc
  have hct : c * (t * t) = -((2 : ZMod p) / (β ⬝ᵥ β)) := by
    field_simp
    linear_combination hc
  ext i j
  simp only [reflMat_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  have : c * (t * β i * (t * β j)) = -((2 : ZMod p) / (β ⬝ᵥ β)) * (β i * β j) := by
    rw [← hct]; ring
  linear_combination this

theorem mulVec_refl (c : ZMod p) (u α : Fin 3 → ZMod p) (i : Fin 3) :
    ((((1 : Matrix (Fin 3) (Fin 3) (ZMod p)) + c • Matrix.vecMulVec u u) *ᵥ α) i =
      α i + c * (u i * (u ⬝ᵥ α))) := by
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply, Matrix.vecMulVec_apply,
      Matrix.add_apply] <;> ring

theorem eq_reflMat_of_normalizes (hp5 : 5 ≤ p) (M : Matrix (Fin 3) (Fin 3) (ZMod p))
    (hM2 : M * M = 1) (u φ : Fin 3 → ZMod p) (hu : u ≠ 0) (hφ : φ ≠ 0)
    (hM : M = 1 + Matrix.vecMulVec u φ)
    (hnorm : ∀ α : Fin 3 → ZMod p, IsRoot α →
      ∃ β, IsRoot β ∧ M * reflMat α = reflMat β * M) :
    ∃ β, IsRoot β ∧ M = reflMat β := by
  have h2 := two_ne_zero_of_five_le (p := p) hp5
  have hkey : ∀ α : Fin 3 → ZMod p, IsRoot α →
      (∃ κ : ZMod p, Mᵀ *ᵥ α = κ • (M *ᵥ α)) ∧ ∃ i, (M *ᵥ α) i = 0 := by
    intro α hα
    obtain ⟨β, hβ, h⟩ := hnorm α hα
    exact key_root hp5 M hM2 hα hβ h
  have hA : ∀ α : Fin 3 → ZMod p, IsRoot α → ∃ κ : ZMod p, (M * Mᵀ) *ᵥ α = κ • α := by
    intro α hα
    obtain ⟨⟨κ, hκ⟩, -⟩ := hkey α hα
    refine ⟨κ, ?_⟩
    rw [← Matrix.mulVec_mulVec, hκ, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hM2,
      Matrix.one_mulVec]
  obtain ⟨κ, hκ⟩ := scalar_of_roots _ hA
  have hB : Mᵀ = κ • M := by
    have h1 : M * (M * Mᵀ) = Mᵀ := by rw [← Matrix.mul_assoc, hM2, Matrix.one_mul]
    rw [← h1, hκ, Matrix.mul_smul, Matrix.mul_one]
  have hM0 : M ≠ 0 := by
    intro h0
    rw [h0, Matrix.zero_mul] at hM2
    have := congrFun (congrFun hM2 0) 0
    simp at this
  have hκ2 : κ = 1 ∨ κ = -1 := by
    have h' : M = κ • Mᵀ := by
      have := congrArg Matrix.transpose hB
      rwa [Matrix.transpose_transpose, Matrix.transpose_smul] at this
    have h3 : M = (κ * κ) • M := by
      calc M = κ • Mᵀ := h'
        _ = κ • (κ • M) := by rw [hB]
        _ = (κ * κ) • M := (mul_smul κ κ M).symm
    have h4 : (κ * κ - 1) • M = 0 := by
      rw [sub_smul, one_smul, ← h3, sub_self]
    obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hM0 (Matrix.ext fun i j => hcon i j)
    have h5 := congrFun (congrFun h4 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h5
    rcases mul_eq_zero.mp h5 with h6 | h6
    · exact mul_self_eq_one_iff.mp (sub_eq_zero.mp h6)
    · exact absurd h6 hij
  have hd := dot_eq_neg_two hM2 hu hφ hM
  rcases hκ2 with hκ1 | hκ1
  ·
    subst hκ1
    have hsym : ∀ i j, u i * φ j = u j * φ i := by
      intro i j
      have h1 := congrFun (congrFun hB i) j
      simp only [Matrix.transpose_apply, one_smul] at h1
      rw [hM] at h1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply] at h1
      by_cases hij : i = j
      · subst hij; rfl
      · have hji : ¬ j = i := fun h => hij h.symm
        simp [hij, hji] at h1
        linear_combination -h1
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hu
    have hi₀' : u i₀ ≠ 0 := hi₀
    set c : ZMod p := φ i₀ / u i₀ with hcdef
    have hφc : φ = c • u := by
      funext j
      have := hsym i₀ j
      simp only [Pi.smul_apply, smul_eq_mul, hcdef]
      field_simp
      linear_combination this
    have hM' : M = 1 + c • Matrix.vecMulVec u u := by
      rw [hM, hφc, Matrix.vecMulVec_smul]
    have hc : c * (u ⬝ᵥ u) = -2 := by
      rw [hφc, smul_dotProduct, smul_eq_mul] at hd
      exact hd
    have hzero : ∀ α : Fin 3 → ZMod p, IsRoot α → ∃ i, α i + c * (u i * (u ⬝ᵥ α)) = 0 := by
      intro α hα
      obtain ⟨-, i, hi⟩ := hkey α hα
      refine ⟨i, ?_⟩
      rw [← mulVec_refl c u α i, ← hM']
      exact hi
    obtain ⟨t, β, hβ, ht, hut⟩ := root_of_zero hp5 hu hc hzero
    exact ⟨β, hβ, by rw [hM']; exact refl_of_smul hp5 hβ hut hc⟩
  ·
    exfalso
    subst hκ1
    have hdiag : ∀ i, 1 + u i * φ i = 0 := by
      intro i
      have h1 := congrFun (congrFun hB i) i
      simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h1
      rw [hM] at h1
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply, ite_true] at h1
      have h3 : (2 : ZMod p) * (1 + u i * φ i) = 0 := by linear_combination h1
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 h2
      · exact h4
    have hd3 : φ ⬝ᵥ u = -3 := by
      simp only [dotProduct, Fin.sum_univ_three]
      linear_combination hdiag 0 + hdiag 1 + hdiag 2
    have : (-2 : ZMod p) = -3 := by rw [← hd, hd3]
    exact one_ne_zero (by linear_combination this : (1 : ZMod p) = 0)

end CFSG.RankThree.PartOne.S13K.ReflAlg
