module

public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.SteinbergCB.GDescent

open Matrix

variable {k : Type*} [Field k] {d : ℕ}

@[expose] def iterMat (s : k ≃+* k) (B : Matrix (Fin d) (Fin d) k) : ℕ → Matrix (Fin d) (Fin d) k
  | 0 => 1
  | n + 1 => B * (iterMat s B n).map s

@[expose] def normIter (s : k ≃+* k) (u : k) : ℕ → k
  | 0 => 1
  | n + 1 => u * s (normIter s u n)

theorem normIter_zero (s : k ≃+* k) (u : k) : normIter s u 0 = 1 := rfl

theorem normIter_succ (s : k ≃+* k) (u : k) (n : ℕ) :
    normIter s u (n + 1) = u * s (normIter s u n) := rfl

theorem iterMat_zero (s : k ≃+* k) (B : Matrix (Fin d) (Fin d) k) : iterMat s B 0 = 1 := rfl

theorem iterMat_succ (s : k ≃+* k) (B : Matrix (Fin d) (Fin d) k) (n : ℕ) :
    iterMat s B (n + 1) = B * (iterMat s B n).map s := rfl

theorem map_pow_succ (s : k ≃+* k) (M : Matrix (Fin d) (Fin d) k) (n : ℕ) :
    (M.map ⇑(s ^ n)).map s = M.map ⇑(s ^ (n + 1)) := by
  rw [Matrix.map_map]
  congr 1
  funext x
  rw [Function.comp_apply, pow_succ', RingAut.mul_apply]

theorem map_one_aut (M : Matrix (Fin d) (Fin d) k) : M.map ⇑(1 : k ≃+* k) = M := by
  rw [RingAut.coe_one, Matrix.map_id]

theorem one_map (s : k ≃+* k) : (1 : Matrix (Fin d) (Fin d) k).map s = 1 :=
  Matrix.map_one _ (map_zero s) (map_one s)

theorem smul_map (s : k ≃+* k) (c : k) (M : Matrix (Fin d) (Fin d) k) :
    (c • M).map s = s c • M.map s :=
  Matrix.map_smul' _ c M (map_mul s)

theorem iterMat_succ' (s : k ≃+* k) (B : Matrix (Fin d) (Fin d) k) (n : ℕ) :
    iterMat s B (n + 1) = iterMat s B n * B.map ⇑(s ^ n) := by
  induction n with
  | zero => rw [iterMat_succ, iterMat_zero, one_map, mul_one, one_mul, pow_zero, map_one_aut]
  | succ n ih =>
    rw [iterMat_succ, ih, Matrix.map_mul, ← mul_assoc, ← iterMat_succ, map_pow_succ, ih]

theorem isUnit_iterMat (s : k ≃+* k) {B : Matrix (Fin d) (Fin d) k} (hB : IsUnit B) (n : ℕ) :
    IsUnit (iterMat s B n) := by
  induction n with
  | zero => exact isUnit_one
  | succ n ih =>
    rw [iterMat_succ]
    refine hB.mul ?_
    rw [Matrix.isUnit_iff_isUnit_det] at ih ⊢
    have h := RingHom.map_det (s : k →+* k) (iterMat s B n)
    rw [RingHom.mapMatrix_apply] at h
    change IsUnit ((iterMat s B n).map (s : k →+* k)).det
    rw [← h]
    exact ih.map _

theorem iterMat_comm (s : k ≃+* k) {B R : Matrix (Fin d) (Fin d) k}
    (hBR : B * R.map s = R * B) (n : ℕ) :
    iterMat s B n * R.map ⇑(s ^ n) = R * iterMat s B n := by
  induction n with
  | zero => rw [iterMat_zero, pow_zero, map_one_aut, one_mul, mul_one]
  | succ n ih =>
    rw [iterMat_succ, ← map_pow_succ, mul_assoc, ← Matrix.map_mul, ih, Matrix.map_mul,
      ← mul_assoc, hBR, mul_assoc]

theorem iterMat_smul (s : k ≃+* k) (u : k) (B : Matrix (Fin d) (Fin d) k) (n : ℕ) :
    iterMat s (u • B) n = normIter s u n • iterMat s B n := by
  induction n with
  | zero => rw [iterMat_zero, iterMat_zero, normIter_zero, one_smul]
  | succ n ih =>
    rw [iterMat_succ, iterMat_succ, ih, smul_map, normIter_succ, smul_mul_assoc, mul_smul_comm,
      smul_smul]

theorem fixed_of_iterMat_eq (s : k ≃+* k) {B : Matrix (Fin d) (Fin d) k} (hB : B ≠ 0) {r : ℕ}
    (hr : s ^ r = 1) {c : k} (hc : iterMat s B r = c • 1) : s c = c := by
  have h1 := iterMat_succ' s B r
  rw [iterMat_succ, hc, hr, map_one_aut, smul_map, one_map, smul_mul_assoc, one_mul,
    mul_smul_comm, mul_one] at h1
  have h2 : (s c - c) • B = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.1 h2 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hB

@[expose] noncomputable def semilinOf (s : k ≃+* k) {B : Matrix (Fin d) (Fin d) k}
    (hB : IsUnit B) : (Fin d → k) ≃+ (Fin d → k) where
  toFun v := B *ᵥ (s ∘ v)
  invFun v := s.symm ∘ (B⁻¹ *ᵥ v)
  left_inv v := by
    have h : B⁻¹ *ᵥ (B *ᵥ (s ∘ v)) = s ∘ v := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det B).1 hB),
        Matrix.one_mulVec]
    funext i
    simp only [Function.comp_apply, h, RingEquiv.symm_apply_apply]
  right_inv v := by
    have h : s ∘ (s.symm ∘ (B⁻¹ *ᵥ v)) = B⁻¹ *ᵥ v := by
      funext i
      simp
    change B *ᵥ (s ∘ (s.symm ∘ (B⁻¹ *ᵥ v))) = v
    rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det B).1 hB),
      Matrix.one_mulVec]
  map_add' v w := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp

theorem semilinOf_apply (s : k ≃+* k) {B : Matrix (Fin d) (Fin d) k} (hB : IsUnit B)
    (v : Fin d → k) : semilinOf s hB v = B *ᵥ (s ∘ v) := rfl

theorem semilinOf_smul (s : k ≃+* k) {B : Matrix (Fin d) (Fin d) k} (hB : IsUnit B) (c : k)
    (v : Fin d → k) : semilinOf s hB (c • v) = s c • semilinOf s hB v := by
  rw [semilinOf_apply, semilinOf_apply, ← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem semilinOf_iterate (s : k ≃+* k) {B : Matrix (Fin d) (Fin d) k} (hB : IsUnit B) (n : ℕ)
    (v : Fin d → k) : (⇑(semilinOf s hB))^[n] v = iterMat s B n *ᵥ (⇑(s ^ n) ∘ v) := by
  induction n with
  | zero =>
    rw [Function.iterate_zero, iterMat_zero, Matrix.one_mulVec, pow_zero, RingAut.coe_one]
    rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, semilinOf_apply, iterMat_succ, ← Matrix.mulVec_mulVec]
    congr 1
    have hcomp : ⇑(s ^ (n + 1)) ∘ v = ⇑s ∘ (⇑(s ^ n) ∘ v) := by
      funext i
      rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, pow_succ',
        RingAut.mul_apply]
    rw [hcomp]
    funext i
    exact RingHom.map_mulVec (s : k →+* k) (iterMat s B n) (⇑(s ^ n) ∘ v) i

theorem exists_fixed_conj [Finite k] {ι : Type*} {r : ℕ} (s : k ≃+* k) (hs : orderOf s = r)
    (hr : 0 < r) (R : ι → Matrix (Fin d) (Fin d) k) {B : Matrix (Fin d) (Fin d) k}
    (hB : IsUnit B) (hBR : ∀ g, B * (R g).map s = R g * B) (hC : iterMat s B r = 1) :
    ∃ P : Matrix (Fin d) (Fin d) k, IsUnit P ∧ ∀ g, (P⁻¹ * R g * P).map s = P⁻¹ * R g * P := by
  classical
  have ha : ∀ (c : k) (v : Fin d → k), semilinOf s hB (c • v) = s c • semilinOf s hB v :=
    semilinOf_smul s hB
  have hsr : s ^ r = 1 := hs ▸ pow_orderOf_eq_one s
  have hah : ∀ v, (⇑(semilinOf s hB))^[r] v = v := by
    intro v
    rw [semilinOf_iterate, hC, hsr, Matrix.one_mulVec, RingAut.coe_one]
    rfl
  obtain ⟨n, b, b₀, hbb₀⟩ :=
    CFSG.GroupTheory.SteinbergBK.exists_semilinear_fixed_basis s hs hr (semilinOf s hB) ha hah
  have hn : n = d := by
    have := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_fin] at this
    exact this.symm
  have hfix : ∀ j, semilinOf s hB (b j) = b j := by
    intro j
    have := (b₀ j).2
    rw [hbb₀] at this
    exact this
  set b' := b.reindex (finCongr hn) with hb'
  have hfix' : ∀ j, semilinOf s hB (b' j) = b' j := fun j => by
    rw [hb', Module.Basis.reindex_apply]
    exact hfix _
  set P : Matrix (Fin d) (Fin d) k := (Pi.basisFun k (Fin d)).toMatrix b' with hP
  have hPij : ∀ i j, P i j = b' j i := by
    intro i j
    rw [hP, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hPu : IsUnit P := by
    have := (Pi.basisFun k (Fin d)).invertibleToMatrix b'
    exact isUnit_of_invertible _
  have hPdet := (Matrix.isUnit_iff_isUnit_det P).1 hPu
  have hBP : B * P.map s = P := by
    ext i j
    have := congrFun (hfix' j) i
    rw [semilinOf_apply] at this
    rw [hPij, ← this, Matrix.mul_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hPij, Function.comp_apply]
  refine ⟨P, hPu, fun g => ?_⟩
  set Q := P⁻¹ * R g * P with hQ
  have hPQ : P * Q = R g * P := by
    rw [hQ, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hPdet, one_mul]
  have h1 : P.map s * Q.map s = (R g).map s * P.map s := by
    rw [← Matrix.map_mul, hPQ, Matrix.map_mul]
  have h2 : P * Q.map s = P * Q := by
    calc P * Q.map s = B * P.map s * Q.map s := by rw [hBP]
      _ = B * (R g).map s * P.map s := by rw [mul_assoc, h1, ← mul_assoc]
      _ = R g * (B * P.map s) := by rw [hBR, mul_assoc]
      _ = P * Q := by rw [hBP, hPQ]
  calc Q.map s = P⁻¹ * (P * Q.map s) := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ hPdet]
    _ = P⁻¹ * (P * Q) := by rw [h2]
    _ = Q := by rw [Matrix.nonsing_inv_mul_cancel_left _ _ hPdet]

end CFSG.Quasithin.SteinbergCB.GDescent
