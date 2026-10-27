module

public import Certificates.Data.CFSGNative.J1.Vec
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Sporadic.J1

open Native Matrix

@[expose] def toV (p d : ℕ) (v : List ℕ) : Fin d → ZMod p := fun i => ((v.getD i.val 0 : ℕ) : ZMod p)

@[expose] def toM (p d : ℕ) (X : List (List ℕ)) : Matrix (Fin d) (Fin d) (ZMod p) :=
  Matrix.of fun i j => (((X.getD i.val []).getD j.val 0 : ℕ) : ZMod p)

theorem dotL_eq_sum : ∀ (n : ℕ) (r c : List ℕ), r.length = n → c.length = n →
    dotL r c = ∑ k ∈ Finset.range n, r.getD k 0 * c.getD k 0 := by
  intro n
  induction n with
  | zero =>
    intro r c hr hc
    rw [List.length_eq_zero_iff] at hr
    subst hr
    simp [dotL]
  | succ n ih =>
    intro r c hr hc
    obtain ⟨a, r, rfl⟩ := List.exists_cons_of_length_eq_add_one hr
    obtain ⟨b, c, rfl⟩ := List.exists_cons_of_length_eq_add_one hc
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hr hc
    rw [dotL, ih r c hr hc, Finset.sum_range_succ']
    simp [Nat.add_comm]

theorem wfM_iff {d : ℕ} {X : List (List ℕ)} :
    wfM d X = true ↔ X.length = d ∧ ∀ r ∈ X, r.length = d := by
  simp [wfM]

theorem wfV_iff {p d : ℕ} {v : List ℕ} : wfV p d v = true ↔ v.length = d ∧ ∀ x ∈ v, x < p := by
  simp [wfV]

theorem getD_of_wfM {d : ℕ} {X : List (List ℕ)} (h : wfM d X = true) (i : ℕ) (hi : i < d) :
    (X.getD i []).length = d := by
  rw [wfM_iff] at h
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact h.2 _ (List.getElem_mem _)

private theorem getD_map_lt {α β : Type*} (f : α → β) {l : List α} {n : ℕ} (d : β) (d' : α)
    (h : n < l.length) : (l.map f).getD n d = f (l.getD n d') := by
  rw [List.getD_eq_getElem (l.map f) d (by simpa using h), List.getElem_map,
    List.getD_eq_getElem l d' h]

theorem toV_mvL {p d : ℕ} {X : List (List ℕ)} {v : List ℕ} (hX : wfM d X = true)
    (hv : v.length = d) : toV p d (mvL p X v) = toM p d X *ᵥ toV p d v := by
  funext i
  have hlen : X.length = d := (wfM_iff.mp hX).1
  have hrow := getD_of_wfM hX i.val i.isLt
  have hi : i.val < X.length := by rw [hlen]; exact i.isLt
  simp only [toV, mvL, mulVec, dotProduct, toM, of_apply]
  rw [getD_map_lt _ 0 [] hi, ZMod.natCast_mod, dotL_eq_sum d _ _ hrow hv]
  push_cast
  exact (Fin.sum_univ_eq_sum_range
    (fun k => (((X.getD i.val []).getD k 0 : ℕ) : ZMod p) * ((v.getD k 0 : ℕ) : ZMod p)) d).symm

theorem mulL_getD {p d : ℕ} {X Y : List (List ℕ)} (hX : wfM d X = true) {i j : ℕ} (hi : i < d)
    (hj : j < d) : ((mulL p d X Y).getD i []).getD j 0 =
      dotL (X.getD i []) (Y.map fun r => r.getD j 0) % p := by
  have hlen : X.length = d := (wfM_iff.mp hX).1
  have hcl : (colsL d Y).length = d := by simp [colsL]
  unfold mulL
  rw [getD_map_lt _ [] [] (show i < X.length by omega),
    getD_map_lt _ 0 [] (show j < (colsL d Y).length by omega)]
  unfold colsL
  rw [getD_map_lt _ [] 0 (show j < (List.range d).length by simpa using hj),
    List.getD_eq_getElem (List.range d) 0 (by simpa using hj), List.getElem_range]

theorem toM_mulL {p d : ℕ} {X Y : List (List ℕ)} (hX : wfM d X = true) (hY : wfM d Y = true) :
    toM p d (mulL p d X Y) = toM p d X * toM p d Y := by
  ext i j
  have hlenY : Y.length = d := (wfM_iff.mp hY).1
  have hrow := getD_of_wfM hX i.val i.isLt
  simp only [toM, of_apply, mul_apply]
  rw [mulL_getD hX i.isLt j.isLt, ZMod.natCast_mod, dotL_eq_sum d _ _ hrow (by simp [hlenY])]
  push_cast
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => (((X.getD i.val []).getD k 0 : ℕ) : ZMod p) *
      ((((Y.map fun r => r.getD j.val 0).getD k 0) : ℕ) : ZMod p)) d]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [getD_map_lt _ 0 [] (show k.val < Y.length by rw [hlenY]; exact k.isLt)]

theorem wfM_mulL {p d : ℕ} {X Y : List (List ℕ)} (hX : wfM d X = true) :
    wfM d (mulL p d X Y) = true := by
  rw [wfM_iff] at hX ⊢
  refine ⟨by simp [mulL, hX.1], fun r hr => ?_⟩
  simp only [mulL, List.mem_map] at hr
  obtain ⟨_, _, rfl⟩ := hr
  simp [colsL]

theorem toM_idL (p d : ℕ) : toM p d (idL d) = 1 := by
  ext i j
  simp only [toM, idL, of_apply, one_apply]
  rw [getD_map_lt _ [] 0 (by simp), List.getD_eq_getElem (List.range d) 0 (by simp),
    List.getElem_range, getD_map_lt _ 0 0 (by simp), List.getD_eq_getElem (List.range d) 0
    (by simp), List.getElem_range]
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_right (fun h' => h (Fin.ext h')), ite_eq_right h]
    simp

theorem wfM_idL (d : ℕ) : wfM d (idL d) = true := by
  rw [wfM_iff]
  refine ⟨by simp [idL], fun r hr => ?_⟩
  simp only [idL, List.mem_map] at hr
  obtain ⟨_, _, rfl⟩ := hr
  simp

theorem toM_powL {p d : ℕ} {X : List (List ℕ)} (hX : wfM d X = true) (e : ℕ) :
    toM p d (powL p d X e) = toM p d X ^ e := by
  have hwf : ∀ e, wfM d (powL p d X e) = true := by
    intro e
    induction e with
    | zero => exact wfM_idL d
    | succ e _ => exact wfM_mulL hX
  induction e with
  | zero => rw [pow_zero]; exact toM_idL p d
  | succ e ih => rw [powL, toM_mulL hX (hwf e), ih, pow_succ']

theorem toV_negL {p d : ℕ} {v : List ℕ} (hv : ∀ x ∈ v, x < p) :
    toV p d (negL p v) = -toV p d v := by
  funext i
  simp only [toV, negL, Pi.neg_apply]
  by_cases hi : i.val < v.length
  · rw [getD_map_lt _ 0 0 hi, ZMod.natCast_mod]
    have hx : v.getD i.val 0 ≤ p := by
      rw [List.getD_eq_getElem _ _ hi]
      exact (hv _ (List.getElem_mem hi)).le
    rw [Nat.cast_sub hx, ZMod.natCast_self, zero_sub]
  · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by omega)]
    simp

theorem toV_inj {p d : ℕ} {v w : List ℕ} (hv : wfV p d v = true) (hw : wfV p d w = true)
    (h : toV p d v = toV p d w) : v = w := by
  rw [wfV_iff] at hv hw
  apply List.ext_getElem (by rw [hv.1, hw.1])
  intro k hk1 hk2
  have := congrFun h ⟨k, by omega⟩
  simp only [toV] at this
  rw [List.getD_eq_getElem _ _ hk1, List.getD_eq_getElem _ _ hk2] at this
  have h1 := hv.2 _ (List.getElem_mem hk1)
  have h2 := hw.2 _ (List.getElem_mem hk2)
  have := congrArg ZMod.val this
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this

theorem toM_colMat_apply {p d : ℕ} (vs : List (List ℕ)) (i j : Fin d) (hj : j.val < vs.length) :
    toM p d (colMat d vs) i j = toV p d (vs.getD j.val []) i := by
  simp only [toM, colMat, toV, of_apply]
  rw [getD_map_lt _ [] 0 (by simp), List.getD_eq_getElem (List.range d) 0 (by simp),
    List.getElem_range, getD_map_lt _ 0 [] hj]

theorem wfM_colMat {d : ℕ} {vs : List (List ℕ)} (hvs : vs.length = d) :
    wfM d (colMat d vs) = true := by
  rw [wfM_iff]
  refine ⟨by simp [colMat], fun r hr => ?_⟩
  simp only [colMat, List.mem_map] at hr
  obtain ⟨_, _, rfl⟩ := hr
  simp [hvs]

theorem toV_ne_zero_of_all {p d : ℕ} {v : List ℕ} (hlen : v.length = d) (hp : ∀ x ∈ v, x < p)
    (h : (v.all fun x => x != 0) = true) (i : Fin d) : toV p d v i ≠ 0 := by
  simp only [List.all_eq_true, bne_iff_ne, ne_eq] at h
  simp only [toV]
  have hi : i.val < v.length := by rw [hlen]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  have h1 := h _ (List.getElem_mem hi)
  have h2 := hp _ (List.getElem_mem hi)
  intro h0
  have := congrArg ZMod.val h0
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h2, ZMod.val_zero] at this
  exact h1 this

section Field

variable {K : Type*} [Field K] {d : ℕ}

theorem eq_smul_one_of_eigen (M P Q : Matrix (Fin d) (Fin d) K) (hQP : Q * P = 1)
    (w : Fin d → K) (hc : ∀ i, (Q *ᵥ w) i ≠ 0)
    (hcol : ∀ j, ∃ c : K, M *ᵥ (fun i => P i j) = c • fun i => P i j)
    (hw : ∃ μ : K, M *ᵥ w = μ • w) : ∃ μ : K, M = μ • 1 := by
  choose lam hlam using hcol
  obtain ⟨μ, hμ⟩ := hw
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hMP : M * P = P * diagonal lam := by
    ext i j
    have := congrFun (hlam j) i
    simp only [mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    rw [mul_apply, this, mul_diagonal, mul_comm]
  set c := Q *ᵥ w with hcdef
  have hwc : P *ᵥ c = w := by rw [hcdef, mulVec_mulVec, hPQ, one_mulVec]
  have key : diagonal lam *ᵥ c = μ • c := by
    have h1 : P *ᵥ (diagonal lam *ᵥ c) = P *ᵥ (μ • c) := by
      rw [mulVec_mulVec, ← hMP, ← mulVec_mulVec, hwc, hμ, mulVec_smul, hwc]
    have h2 : Q *ᵥ (P *ᵥ (diagonal lam *ᵥ c)) = Q *ᵥ (P *ᵥ (μ • c)) := by rw [h1]
    rwa [mulVec_mulVec (diagonal lam *ᵥ c) Q P, mulVec_mulVec (μ • c) Q P, hQP, one_mulVec,
      one_mulVec] at h2
  have hlam' : ∀ j, lam j = μ := by
    intro j
    have := congrFun key j
    simp only [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ (hc j) this
  refine ⟨μ, ?_⟩
  have hdiag : diagonal lam = μ • (1 : Matrix (Fin d) (Fin d) K) := by
    rw [smul_one_eq_diagonal]
    exact congrArg diagonal (funext hlam')
  calc M = M * (P * Q) := by rw [hPQ, mul_one]
    _ = (M * P) * Q := by rw [mul_assoc]
    _ = μ • (P * Q) := by rw [hMP, hdiag, Matrix.mul_smul, mul_one, Matrix.smul_mul]
    _ = μ • 1 := by rw [hPQ]

theorem eq_one_of_fix_cols (M P Q : Matrix (Fin d) (Fin d) K) (hQP : Q * P = 1)
    (hcol : ∀ j, M *ᵥ (fun i => P i j) = fun i => P i j) : M = 1 := by
  have hPQ : P * Q = 1 := mul_eq_one_comm.mp hQP
  have hMP : M * P = P := by
    ext i j
    have := congrFun (hcol j) i
    simp only [mulVec, dotProduct] at this
    rw [mul_apply, this]
  calc M = M * (P * Q) := by rw [hPQ, mul_one]
    _ = (M * P) * Q := by rw [mul_assoc]
    _ = 1 := by rw [hMP, hPQ]

theorem minor_eq_of_vecMulVec_eq {v w : Fin d → K} (h : vecMulVec v v = vecMulVec w w)
    (a b : Fin d) : v a * w b = v b * w a := by
  have hvw : ∀ i j, v i * v j = w i * w j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [vecMulVec_apply] using this
  by_cases hv : ∀ k, v k = 0
  · simp [hv]
  push Not at hv
  obtain ⟨k, hk⟩ := hv
  have hwk : w k ≠ 0 := by
    intro h0
    have := hvw k k
    rw [h0, mul_zero] at this
    exact hk (mul_self_eq_zero.mp this)
  apply mul_right_cancel₀ hwk
  have e1 := hvw a k
  have e2 := hvw b k
  calc v a * w b * w k = v a * (w b * w k) := by ring
    _ = v a * (v b * v k) := by rw [e2]
    _ = v b * (v a * v k) := by ring
    _ = v b * (w a * w k) := by rw [e1]
    _ = v b * w a * w k := by ring

theorem exists_smul_of_vecMulVec_eq {u v : Fin d → K} (h : vecMulVec u u = vecMulVec v v) :
    ∃ c : K, u = c • v := by
  by_cases hv : ∀ k, v k = 0
  · refine ⟨0, funext fun a => ?_⟩
    have := congrFun (congrFun h a) a
    simp only [vecMulVec_apply, hv, mul_zero] at this
    simpa using mul_self_eq_zero.mp this
  push Not at hv
  obtain ⟨k, hk⟩ := hv
  refine ⟨u k / v k, funext fun a => ?_⟩
  have := minor_eq_of_vecMulVec_eq h a k
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination this

end Field

end CFSG.Sporadic.J1
