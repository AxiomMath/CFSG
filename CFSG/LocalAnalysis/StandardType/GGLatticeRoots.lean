module

public import CFSG.LocalAnalysis.StandardType.GGLatticeRootsDefs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.StandardType

section Lattice

variable {m : ℕ}

section Helpers

variable {Q : Matrix (Fin m) (Fin m) ℤ}

private theorem lat_symm (hQ : GGLatForm Q) (v w : Fin m → ℤ) :
    dotProduct v (Q.mulVec w) = dotProduct w (Q.mulVec v) :=
  Matrix.IsSymm.dotProduct_mulVec_comm hQ.1

private theorem lat_nonneg (hQ : GGLatForm Q) (y : Fin m → ℤ) :
    0 ≤ dotProduct y (Q.mulVec y) := by
  by_cases hy : y = 0
  · subst hy; simp
  · exact (hQ.2 y hy).le

private theorem lat_norm_pos (hQ : GGLatForm Q) {w : Fin m → ℤ} (hw : GGLatRoot Q w) :
    0 < dotProduct w (Q.mulVec w) := hQ.2 w hw.1

private theorem cartan_mul {b : Fin m → ℤ} (hb : GGLatRoot Q b) (v : Fin m → ℤ) :
    ggLatCartan Q v b * dotProduct b (Q.mulVec b) = 2 * dotProduct v (Q.mulVec b) :=
  Int.ediv_mul_cancel (hb.2 v)

private theorem lat_cs (hQ : GGLatForm Q) (a b : Fin m → ℤ) :
    (dotProduct a (Q.mulVec b)) ^ 2 ≤
      dotProduct a (Q.mulVec a) * dotProduct b (Q.mulVec b) := by
  by_cases hb : b = 0
  · subst hb; simp
  · have hNb : 0 < dotProduct b (Q.mulVec b) := hQ.2 b hb
    have hx := lat_nonneg hQ
      (dotProduct b (Q.mulVec b) • a - dotProduct a (Q.mulVec b) • b)
    have key : dotProduct
          (dotProduct b (Q.mulVec b) • a - dotProduct a (Q.mulVec b) • b)
          (Q.mulVec (dotProduct b (Q.mulVec b) • a - dotProduct a (Q.mulVec b) • b))
        = dotProduct b (Q.mulVec b) *
          (dotProduct a (Q.mulVec a) * dotProduct b (Q.mulVec b)
            - (dotProduct a (Q.mulVec b)) ^ 2) := by
      simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
        dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [lat_symm hQ b a]
      ring
    rw [key] at hx
    nlinarith [hx, hNb]

private theorem pair_mul_norm (hQ : GGLatForm Q) {a b : Fin m → ℤ} (ha : GGLatRoot Q a)
    (hb : GGLatRoot Q b) :
    ggLatCartan Q a b * ggLatCartan Q b a *
        (dotProduct a (Q.mulVec a) * dotProduct b (Q.mulVec b)) =
      4 * (dotProduct a (Q.mulVec b)) ^ 2 := by
  have h1 := cartan_mul hb a
  have h2 := cartan_mul ha b
  rw [lat_symm hQ b a] at h2
  calc ggLatCartan Q a b * ggLatCartan Q b a *
        (dotProduct a (Q.mulVec a) * dotProduct b (Q.mulVec b))
      = (ggLatCartan Q a b * dotProduct b (Q.mulVec b))
        * (ggLatCartan Q b a * dotProduct a (Q.mulVec a)) := by ring
    _ = (2 * dotProduct a (Q.mulVec b)) * (2 * dotProduct a (Q.mulVec b)) := by rw [h1, h2]
    _ = 4 * (dotProduct a (Q.mulVec b)) ^ 2 := by ring

private theorem ggLatCartan_sub_smul (hQ : GGLatForm Q) {f : Fin m → ℤ} (hf : GGLatRoot Q f)
    (u v : Fin m → ℤ)
    (k : ℤ) : ggLatCartan Q (u - k • v) f = ggLatCartan Q u f - k * ggLatCartan Q v f := by
  apply mul_right_cancel₀ (ne_of_gt (lat_norm_pos hQ hf))
  have hL := cartan_mul hf (u - k • v)
  have hu := cartan_mul hf u
  have hv := cartan_mul hf v
  rw [sub_mul, hL, hu]
  simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  linear_combination k * hv

private theorem ggLatRefl_isometry (hQ : GGLatForm Q) {f : Fin m → ℤ} (hf : GGLatRoot Q f)
    (y z : Fin m → ℤ) :
    dotProduct (ggLatRefl Q f y) (Q.mulVec (ggLatRefl Q f z)) = dotProduct y (Q.mulVec z) := by
  have hy := cartan_mul hf y
  have hz := cartan_mul hf z
  have hsym : dotProduct f (Q.mulVec z) = dotProduct z (Q.mulVec f) := lat_symm hQ f z
  apply mul_left_cancel₀ (a := (2 : ℤ)) (by norm_num)
  simp only [ggLatRefl, Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
    dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [hsym]
  linear_combination (ggLatCartan Q z f) * hy + (ggLatCartan Q y f) * hz

private theorem cartan_self (hQ : GGLatForm Q) {f : Fin m → ℤ} (hf : GGLatRoot Q f) :
    ggLatCartan Q f f = 2 := by
  have h := cartan_mul hf f
  refine mul_right_cancel₀ (ne_of_gt (lat_norm_pos hQ hf)) ?_
  rw [h]

private theorem ggLatRefl_involutive (hQ : GGLatForm Q) {f : Fin m → ℤ} (hf : GGLatRoot Q f)
    (y : Fin m → ℤ) : ggLatRefl Q f (ggLatRefl Q f y) = y := by
  have hff : ggLatCartan Q f f = 2 := cartan_self hQ hf
  simp only [ggLatRefl]
  rw [ggLatCartan_sub_smul hQ hf y f (ggLatCartan Q y f), hff]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem ggLatRefl_sub_smul (hQ : GGLatForm Q) {f : Fin m → ℤ} (hf : GGLatRoot Q f)
    (u v : Fin m → ℤ) (k : ℤ) :
    ggLatRefl Q f (u - k • v) = ggLatRefl Q f u - k • ggLatRefl Q f v := by
  simp only [ggLatRefl]
  rw [ggLatCartan_sub_smul hQ hf u v k]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem lat_pair_refl (hQ : GGLatForm Q) {a f : Fin m → ℤ} (hf : GGLatRoot Q f)
    (y : Fin m → ℤ) :
    dotProduct y (Q.mulVec (ggLatRefl Q f a)) =
      dotProduct (ggLatRefl Q f y) (Q.mulVec a) := by
  calc dotProduct y (Q.mulVec (ggLatRefl Q f a))
      = dotProduct (ggLatRefl Q f (ggLatRefl Q f y)) (Q.mulVec (ggLatRefl Q f a)) := by
        rw [ggLatRefl_involutive hQ hf y]
    _ = dotProduct (ggLatRefl Q f y) (Q.mulVec a) :=
        ggLatRefl_isometry hQ hf (ggLatRefl Q f y) a

private theorem ggLatRefl_root (hQ : GGLatForm Q) {a f : Fin m → ℤ} (ha : GGLatRoot Q a)
    (hf : GGLatRoot Q f) : GGLatRoot Q (ggLatRefl Q f a) := by
  have hnorm : dotProduct (ggLatRefl Q f a) (Q.mulVec (ggLatRefl Q f a))
      = dotProduct a (Q.mulVec a) := ggLatRefl_isometry hQ hf a a
  have hpair : ∀ y, dotProduct y (Q.mulVec (ggLatRefl Q f a))
      = dotProduct (ggLatRefl Q f y) (Q.mulVec a) := fun y => lat_pair_refl (a := a) hQ hf y
  refine ⟨?_, ?_⟩
  · intro hzero
    have hN0 : dotProduct (ggLatRefl Q f a) (Q.mulVec (ggLatRefl Q f a)) = 0 := by
      rw [hzero]; simp
    rw [hnorm] at hN0
    exact absurd hN0 (ne_of_gt (lat_norm_pos hQ ha))
  · intro y
    rw [hnorm, hpair y]
    exact ha.2 (ggLatRefl Q f y)

private theorem cartan_refl (hQ : GGLatForm Q) {a f : Fin m → ℤ} (ha : GGLatRoot Q a)
    (hf : GGLatRoot Q f) (y : Fin m → ℤ) :
    ggLatCartan Q y (ggLatRefl Q f a) = ggLatCartan Q (ggLatRefl Q f y) a := by
  have hfa : GGLatRoot Q (ggLatRefl Q f a) := ggLatRefl_root hQ ha hf
  have h1 := cartan_mul hfa y
  have h2 := cartan_mul ha (ggLatRefl Q f y)
  have hnorm : dotProduct (ggLatRefl Q f a) (Q.mulVec (ggLatRefl Q f a))
      = dotProduct a (Q.mulVec a) := ggLatRefl_isometry hQ hf a a
  have hpair := lat_pair_refl (a := a) hQ hf y
  apply mul_right_cancel₀ (ne_of_gt (lat_norm_pos hQ hfa))
  rw [h1, hpair, hnorm, h2]

private theorem ggLatRefl_conj (hQ : GGLatForm Q) {a f : Fin m → ℤ} (ha : GGLatRoot Q a)
    (hf : GGLatRoot Q f) (y : Fin m → ℤ) :
    ggLatRefl Q (ggLatRefl Q f a) y = ggLatRefl Q f (ggLatRefl Q a (ggLatRefl Q f y)) := by
  have hc : ggLatCartan Q (ggLatRefl Q f y) a = ggLatCartan Q y (ggLatRefl Q f a) :=
    (cartan_refl hQ ha hf y).symm
  have hkey : ggLatRefl Q f (ggLatRefl Q f y - ggLatCartan Q (ggLatRefl Q f y) a • a)
      = y - ggLatCartan Q (ggLatRefl Q f y) a • ggLatRefl Q f a := by
    rw [ggLatRefl_sub_smul hQ hf (ggLatRefl Q f y) a
        (ggLatCartan Q (ggLatRefl Q f y) a),
      ggLatRefl_involutive hQ hf y]
  rw [show ggLatRefl Q a (ggLatRefl Q f y)
      = ggLatRefl Q f y - ggLatCartan Q (ggLatRefl Q f y) a • a from rfl, hkey, hc]
  simp only [ggLatRefl]

private theorem pair_refl (hQ : GGLatForm Q) {a b f : Fin m → ℤ} (ha : GGLatRoot Q a)
    (hb : GGLatRoot Q b) (hf : GGLatRoot Q f) :
    ggLatCartan Q (ggLatRefl Q f a) b * ggLatCartan Q b (ggLatRefl Q f a)
      = ggLatCartan Q a b * ggLatCartan Q b a
        - ggLatCartan Q a b * ggLatCartan Q b f * ggLatCartan Q f a
        - ggLatCartan Q b a * ggLatCartan Q f b * ggLatCartan Q a f
        + (ggLatCartan Q a f * ggLatCartan Q f a)
          * (ggLatCartan Q f b * ggLatCartan Q b f) := by
  have h1 : ggLatCartan Q (ggLatRefl Q f a) b
      = ggLatCartan Q a b - ggLatCartan Q a f * ggLatCartan Q f b :=
    ggLatCartan_sub_smul hQ hb a f (ggLatCartan Q a f)
  have h2 : ggLatCartan Q b (ggLatRefl Q f a)
      = ggLatCartan Q b a - ggLatCartan Q b f * ggLatCartan Q f a := by
    rw [cartan_refl hQ ha hf b]
    exact ggLatCartan_sub_smul hQ ha b f (ggLatCartan Q b f)
  rw [h1, h2]
  ring

private theorem ggLatRefl_eq_of_pair_four (hQ : GGLatForm Q) {a b : Fin m → ℤ}
    (ha : GGLatRoot Q a) (hb : GGLatRoot Q b)
    (h4 : ggLatCartan Q a b * ggLatCartan Q b a = 4) (y : Fin m → ℤ) :
    ggLatRefl Q b y = ggLatRefl Q a y := by
  set Na := dotProduct a (Q.mulVec a) with hNa
  set Nb := dotProduct b (Q.mulVec b) with hNb
  set Bab := dotProduct a (Q.mulVec b) with hBab
  have hNa' : 0 < Na := by rw [hNa]; exact lat_norm_pos hQ ha
  have hNb' : 0 < Nb := by rw [hNb]; exact lat_norm_pos hQ hb
  have hB2 : Bab ^ 2 = Na * Nb := by
    have hpn := pair_mul_norm hQ ha hb
    rw [← hNa, ← hNb, ← hBab] at hpn
    nlinarith [hpn, h4]
  have hvec : Na • b = Bab • a := by
    have hzero : dotProduct (Na • b - Bab • a) (Q.mulVec (Na • b - Bab • a)) = 0 := by
      have key : dotProduct (Na • b - Bab • a) (Q.mulVec (Na • b - Bab • a))
          = Na * (Na * Nb - Bab ^ 2) := by
        simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
          dotProduct_smul, smul_dotProduct, smul_eq_mul]
        rw [lat_symm hQ b a, ← hNa, ← hNb, ← hBab]
        ring
      rw [key, hB2]; ring
    by_contra hx
    have hx' : Na • b - Bab • a ≠ 0 := sub_ne_zero.mpr hx
    have := hQ.2 _ hx'
    rw [hzero] at this
    exact lt_irrefl 0 this
  have hcoord : ∀ i, Na * b i = Bab * a i := fun i => by
    have := congrFun hvec i
    simpa [Pi.smul_apply, smul_eq_mul] using this
  have hBab_ne : Bab ≠ 0 := by
    intro h
    have hpos : 0 < Bab ^ 2 := by rw [hB2]; exact mul_pos hNa' hNb'
    rw [h] at hpos
    norm_num at hpos
  have hbcoord : ∀ i, Bab * b i = Nb * a i := fun i => by
    have h1 := hcoord i
    have hmul : Na * (Bab * b i - Nb * a i) = 0 := by
      linear_combination Bab * h1 + (a i) * hB2
    rcases mul_eq_zero.mp hmul with h0 | h0
    · exact absurd h0 (ne_of_gt hNa')
    · linarith
  have hNaB : Na * dotProduct y (Q.mulVec b) = Bab * dotProduct y (Q.mulVec a) := by
    have h := congrArg (fun v => dotProduct y (Q.mulVec v)) hvec
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul] at h
    simpa [smul_eq_mul] using h
  have hBa_eq : ∀ i, dotProduct y (Q.mulVec b) * a i
      = dotProduct y (Q.mulVec a) * b i := fun i => by
    have h := hcoord i
    have hkey : Na * (dotProduct y (Q.mulVec b) * a i
        - dotProduct y (Q.mulVec a) * b i) = 0 := by
      linear_combination (a i) * hNaB - (dotProduct y (Q.mulVec a)) * h
    rcases mul_eq_zero.mp hkey with h0 | h0
    · exact absurd h0 (ne_of_gt hNa')
    · linarith
  have hcy : ∀ i, ggLatCartan Q y b * b i = ggLatCartan Q y a * a i := fun i => by
    have hyb := cartan_mul hb y
    have hya := cartan_mul ha y
    rw [← hNb] at hyb
    rw [← hNa] at hya
    have hbi := hbcoord i
    have hai := hcoord i
    have hxy : Bab * (ggLatCartan Q y b * b i) = Bab * (ggLatCartan Q y a * a i) := by
      linear_combination (ggLatCartan Q y b) * hbi + (a i) * hyb
        + (ggLatCartan Q y a) * hai - (b i) * hya + 2 * hBa_eq i
    exact mul_left_cancel₀ hBab_ne hxy
  ext i
  simp only [ggLatRefl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcy i]

end Helpers

theorem ggLat_pair_bound {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q) {a b : Fin m → ℤ}
    (ha : GGLatRoot Q a) (hb : GGLatRoot Q b) :
    0 ≤ ggLatCartan Q a b * ggLatCartan Q b a ∧ ggLatCartan Q a b * ggLatCartan Q b a ≤ 4 := by
  have hM : 0 < dotProduct a (Q.mulVec a) * dotProduct b (Q.mulVec b) :=
    mul_pos (lat_norm_pos hQ ha) (lat_norm_pos hQ hb)
  have hpm := pair_mul_norm hQ ha hb
  have hcs := lat_cs hQ a b
  constructor <;> nlinarith [hpm, hcs, hM]

theorem ggLat_cycle_comm {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q) {a b f : Fin m → ℤ}
    (ha : GGLatRoot Q a) (hb : GGLatRoot Q b) (hf : GGLatRoot Q f) :
    ggLatCartan Q b a * ggLatCartan Q f b * ggLatCartan Q a f =
      ggLatCartan Q a b * ggLatCartan Q b f * ggLatCartan Q f a := by
  have hK : dotProduct a (Q.mulVec a) * dotProduct b (Q.mulVec b)
      * dotProduct f (Q.mulVec f) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (ne_of_gt (lat_norm_pos hQ ha)) (ne_of_gt (lat_norm_pos hQ hb)))
      (ne_of_gt (lat_norm_pos hQ hf))
  apply mul_right_cancel₀ hK
  have h1 := cartan_mul hb a
  have h2 := cartan_mul hf b
  have h3 := cartan_mul ha f
  have h4 := cartan_mul hf a
  have h5 := cartan_mul hb f
  have h6 := cartan_mul ha b
  have s1 : dotProduct b (Q.mulVec a) = dotProduct a (Q.mulVec b) := lat_symm hQ b a
  have s2 : dotProduct f (Q.mulVec b) = dotProduct b (Q.mulVec f) := lat_symm hQ f b
  have s3 : dotProduct a (Q.mulVec f) = dotProduct f (Q.mulVec a) := lat_symm hQ a f
  calc (ggLatCartan Q b a * ggLatCartan Q f b * ggLatCartan Q a f)
        * (dotProduct a (Q.mulVec a) * dotProduct b (Q.mulVec b)
          * dotProduct f (Q.mulVec f))
      = (ggLatCartan Q b a * dotProduct a (Q.mulVec a))
        * (ggLatCartan Q f b * dotProduct b (Q.mulVec b))
        * (ggLatCartan Q a f * dotProduct f (Q.mulVec f)) := by ring
    _ = (2 * dotProduct b (Q.mulVec a)) * (2 * dotProduct f (Q.mulVec b))
        * (2 * dotProduct a (Q.mulVec f)) := by rw [h6, h5, h4]
    _ = 8 * dotProduct a (Q.mulVec b) * dotProduct b (Q.mulVec f)
        * dotProduct f (Q.mulVec a) := by rw [s1, s2, s3]; ring
    _ = (ggLatCartan Q a b * dotProduct b (Q.mulVec b))
        * (ggLatCartan Q b f * dotProduct f (Q.mulVec f))
        * (ggLatCartan Q f a * dotProduct a (Q.mulVec a)) := by rw [h1, h2, h3]; ring
    _ = (ggLatCartan Q a b * ggLatCartan Q b f * ggLatCartan Q f a)
        * (dotProduct a (Q.mulVec a) * dotProduct b (Q.mulVec b)
          * dotProduct f (Q.mulVec f)) := by ring

theorem ggLat_gram_trichotomy {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q)
    {a b f : Fin m → ℤ} (ha : GGLatRoot Q a) (hb : GGLatRoot Q b) (hf : GGLatRoot Q f) {n : ℤ}
    (hn : n = 1 ∨ n = 2 ∨ n = 3)
    (haf : ggLatCartan Q a f * ggLatCartan Q f a = n)
    (hbf : ggLatCartan Q b f * ggLatCartan Q f b = n) :
    (ggLatCartan Q b a * ggLatCartan Q f b * ggLatCartan Q a f = 0 ∨
      ggLatCartan Q b a * ggLatCartan Q f b * ggLatCartan Q a f = n) ∨
    (∀ y, ggLatRefl Q b y = ggLatRefl Q a y) ∨
    (∀ y, ggLatRefl Q b y = ggLatRefl Q f (ggLatRefl Q a (ggLatRefl Q f y))) := by
  set P := ggLatCartan Q a b * ggLatCartan Q b a with hP
  set G := ggLatCartan Q b a * ggLatCartan Q f b * ggLatCartan Q a f with hG
  set G' := ggLatCartan Q a b * ggLatCartan Q b f * ggLatCartan Q f a with hG'
  have hbd := ggLat_pair_bound hQ ha hb
  have hP0 : 0 ≤ P := by rw [hP]; exact hbd.1
  have hP4 : P ≤ 4 := by rw [hP]; exact hbd.2
  have hGG' : G = G' := by rw [hG, hG']; exact ggLat_cycle_comm hQ ha hb hf
  have hfb : ggLatCartan Q f b * ggLatCartan Q b f = n := by rw [mul_comm]; exact hbf
  have hGsq : G ^ 2 = P * n ^ 2 := by
    have h : G * G' = P * n ^ 2 := by
      rw [hG, hG', hP]
      have e1 : (ggLatCartan Q b a * ggLatCartan Q f b * ggLatCartan Q a f)
            * (ggLatCartan Q a b * ggLatCartan Q b f * ggLatCartan Q f a)
          = (ggLatCartan Q a b * ggLatCartan Q b a)
            * (ggLatCartan Q f b * ggLatCartan Q b f)
            * (ggLatCartan Q a f * ggLatCartan Q f a) := by ring
      rw [e1, hfb, haf, pow_two]
      ring
    rw [← hGG'] at h
    rwa [pow_two]
  have hPcases : P = 0 ∨ P = 1 ∨ P = 4 := by
    have hn2 : n ^ 2 ≤ 9 := by rcases hn with rfl | rfl | rfl <;> norm_num
    have h36 : G ^ 2 ≤ (6 : ℤ) ^ 2 := by
      calc G ^ 2 = P * n ^ 2 := hGsq
        _ ≤ 4 * 9 := mul_le_mul hP4 hn2 (sq_nonneg n) (by norm_num)
        _ = (6 : ℤ) ^ 2 := by norm_num
    have hGb := abs_le_of_sq_le_sq' h36 (by norm_num : (0 : ℤ) ≤ 6)
    have hGlo : -6 ≤ G := hGb.1
    have hGhi : G ≤ 6 := hGb.2
    rcases hn with rfl | rfl | rfl <;>
      · interval_cases P <;> interval_cases G <;> (norm_num at hGsq) <;> norm_num
  rcases hPcases with hPz | hPo | hPf
  · left; left
    have hG0 : G = 0 := by
      have h : G ^ 2 = 0 := by rw [hGsq, hPz]; ring
      exact sq_eq_zero_iff.mp h
    exact hG0
  · have hGn : G = n ∨ G = -n := by
      have h : G ^ 2 = n ^ 2 := by rw [hGsq, hPo]; ring
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h
    rcases hGn with hGn | hGn
    · left; right; exact hGn
    · right; right
      intro y
      have hfa : GGLatRoot Q (ggLatRefl Q f a) := ggLatRefl_root hQ ha hf
      have hG'n : G' = -n := by rw [← hGG', hGn]
      have hpair : ggLatCartan Q (ggLatRefl Q f a) b
          * ggLatCartan Q b (ggLatRefl Q f a) = (n + 1) ^ 2 := by
        rw [pair_refl hQ ha hb hf, ← hP, ← hG, ← hG', haf, hfb, hPo, hGn, hG'n]
        ring
      have hbnd := ggLat_pair_bound hQ hfa hb
      have hn1 : n = 1 := by
        rcases hn with rfl | rfl | rfl
        · rfl
        · exfalso; nlinarith [hpair, hbnd.2]
        · exfalso; nlinarith [hpair, hbnd.2]
      have hp4 : ggLatCartan Q (ggLatRefl Q f a) b
          * ggLatCartan Q b (ggLatRefl Q f a) = 4 := by
        rw [hpair, hn1]; norm_num
      rw [ggLatRefl_eq_of_pair_four hQ hfa hb hp4 y]
      exact ggLatRefl_conj hQ ha hf y
  · right; left
    intro y
    exact ggLatRefl_eq_of_pair_four hQ ha hb (by rw [← hP]; exact hPf) y

theorem ggLat_eq_of_cast_eq {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {P n : ℤ} (hP0 : 0 ≤ P)
    (hP4 : P ≤ 4) (hn1 : 1 ≤ n) (hn3 : n ≤ 3) (h : (P : ZMod p) = n) : P = n := by
  have hdvd : (p : ℤ) ∣ n - P := (ZMod.intCast_eq_intCast_iff_dvd_sub P n p).mp h
  have habs : |n - P| ≤ 3 := by
    rw [abs_le]
    constructor <;> linarith
  have hp : (3 : ℤ) < (p : ℤ) := by
    have : (5 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp5
    linarith
  exact (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd (lt_of_le_of_lt habs hp))).symm

end Lattice

end CFSG.StandardType
