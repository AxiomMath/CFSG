module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KFSU5

open Matrix

@[expose] def blockOf {ι : Type} {K : Type} (J : Finset ι) (M : Matrix ι ι K) : Matrix J J K :=
  M.submatrix (fun j : J => (j : ι)) (fun j : J => (j : ι))

theorem blockOf_one {ι : Type} [DecidableEq ι] {K : Type} [Zero K] [One K] (J : Finset ι) :
    blockOf J (1 : Matrix ι ι K) = 1 :=
  Matrix.submatrix_one _ Subtype.val_injective

theorem blockOf_mul {ι : Type} [Fintype ι] {K : Type} [NonUnitalNonAssocSemiring K] (J : Finset ι)
    {M N : Matrix ι ι K} (hM : ∀ j ∈ J, ∀ k ∉ J, M j k = 0) :
    blockOf J (M * N) = blockOf J M * blockOf J N := by
  ext j l
  simp only [blockOf, Matrix.submatrix_apply, Matrix.mul_apply]
  have h1 : ∑ k ∈ J, M j k * N k l = ∑ k, M j k * N k l :=
    Finset.sum_subset (Finset.subset_univ J) (fun k _ hk => by rw [hM j j.2 k hk, zero_mul])
  rw [← h1]
  exact (Finset.sum_coe_sort J (fun k => M j k * N k l)).symm

@[expose] noncomputable def blockDet {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (J : Finset ι) (D : Subgroup (GL ι K))
    (hD : ∀ y ∈ D, ∀ j ∈ J, ∀ k ∉ J, ((y : GL ι K) : Matrix ι ι K) j k = 0) : D →* K where
  toFun y := (blockOf J ((y : GL ι K) : Matrix ι ι K)).det
  map_one' := by simp [blockOf_one]
  map_mul' y z := by
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [blockOf_mul J (hD y y.2), Matrix.det_mul]

theorem det_blockOf_of_isDiag {ι : Type} [DecidableEq ι] {K : Type} [CommRing K] (J : Finset ι)
    {M : Matrix ι ι K} (hM : M.IsDiag) : (blockOf J M).det = ∏ j ∈ J, M j j := by
  have : blockOf J M = Matrix.diagonal (fun j : J => M j j) := by
    ext j l
    by_cases hjl : j = l
    · subst hjl; simp [blockOf]
    · have : (j : ι) ≠ l := fun h => hjl (Subtype.ext h)
      simp [blockOf, Matrix.diagonal_apply_ne _ hjl, hM this]
  rw [this, Matrix.det_diagonal]
  exact Finset.prod_coe_sort J (fun j => M j j)

section Centralizer

variable {n : ℕ} {K : Type} [Field K]

abbrev entry (a : GL (Fin n) K) (i j : Fin n) : K :=
  ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j

@[expose] noncomputable def blk (Ã : Subgroup (GL (Fin n) K)) (i : Fin n) : Finset (Fin n) :=
  open scoped _root_.Classical in Finset.univ.filter fun j => ∀ a ∈ Ã, entry a j j = entry a i i

theorem mem_blk {Ã : Subgroup (GL (Fin n) K)} {i j : Fin n} :
    j ∈ blk Ã i ↔ ∀ a ∈ Ã, entry a j j = entry a i i := by
  classical
  simp [blk]

theorem isDiag_mul_apply {M N : Matrix (Fin n) (Fin n) K} (hM : M.IsDiag) (j k : Fin n) :
    (M * N) j k = M j j * N j k := by
  rw [← hM.diagonal_diag, Matrix.diagonal_mul]
  simp [Matrix.diag]

theorem mul_isDiag_apply {M N : Matrix (Fin n) (Fin n) K} (hN : N.IsDiag) (j k : Fin n) :
    (M * N) j k = M j k * N k k := by
  rw [← hN.diagonal_diag, Matrix.mul_diagonal]
  simp [Matrix.diag]

theorem entry_eq_zero_of_mem_centralizer {Ã : Subgroup (GL (Fin n) K)}
    (hdiag : ∀ a ∈ Ã, ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    {y : GL (Fin n) K} (hy : y ∈ Subgroup.centralizer (Ã : Set (GL (Fin n) K)))
    {i j k : Fin n} (hj : j ∈ blk Ã i) (hk : k ∉ blk Ã i) : entry y j k = 0 := by
  rw [mem_blk] at hj hk
  push Not at hk
  obtain ⟨a, ha, hak⟩ := hk
  have hcomm := Subgroup.mem_centralizer_iff.mp hy a ha
  have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) j k) hcomm
  simp only [Units.val_mul] at h1
  rw [isDiag_mul_apply (hdiag a ha), mul_isDiag_apply (hdiag a ha)] at h1
  have h2 : entry y j k * (entry a k k - entry a j j) = 0 := by
    have : entry a j j * entry y j k = entry y j k * entry a k k := h1
    linear_combination -this
  rcases mul_eq_zero.mp h2 with h | h
  · exact h
  · exfalso
    exact hak (by rw [← hj a ha]; exact (sub_eq_zero.mp h))

theorem entry_pow_of_isDiag {M : Matrix (Fin n) (Fin n) K} (hM : M.IsDiag) (m : ℕ) (i : Fin n) :
    (M ^ m) i i = (M i i) ^ m := by
  rw [← hM.diagonal_diag, Matrix.diagonal_pow]
  simp [Matrix.diag]

theorem eq_one_of_pow_two_pow_eq_one [Finite K] (hodd : Odd (Nat.card K - 1)) {x : K} {k : ℕ}
    (h : x ^ 2 ^ k = 1) : x = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hx : x ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at h
    exact zero_ne_one h
  have h1 := FiniteField.pow_card_sub_one_eq_one x hx
  rw [← Nat.card_eq_fintype_card] at h1
  have hcop : Nat.gcd (2 ^ k) (Nat.card K - 1) = 1 :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have := pow_gcd_eq_one.mpr ⟨h, h1⟩
  rwa [hcop, pow_one] at this

theorem eq_one_of_mem_closure_twoElements [Finite K] (hodd : Odd (Nat.card K - 1)) {p : ℕ}
    (hp : p.Prime) (hnp : n ≤ p) (Ã : Subgroup (GL (Fin n) K))
    (hdiag : ∀ a ∈ Ã, ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    (hexp : ∀ a ∈ Ã, a ^ p = 1) (hnot : ∃ a ∈ Ã, ∃ i j : Fin n, entry a i i ≠ entry a j j)
    {x : GL (Fin n) K}
    (hx : x ∈ Subgroup.closure {y : GL (Fin n) K |
      y ∈ Subgroup.centralizer (Ã : Set (GL (Fin n) K)) ∧ ∃ k : ℕ, orderOf y = 2 ^ k})
    (hxA : x ∈ Ã) : x = 1 := by
  classical
  set D : Subgroup (GL (Fin n) K) := Subgroup.centralizer (Ã : Set (GL (Fin n) K)) with hD
  have hxi : ∀ i : Fin n, entry x i i = 1 := by
    intro i
    set J := blk Ã i with hJ
    have hDJ : ∀ y ∈ D, ∀ j ∈ J, ∀ k ∉ J,
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j k = 0 :=
      fun y hy j hj k hk => entry_eq_zero_of_mem_centralizer hdiag hy hj hk
    set ψ := blockDet J D hDJ with hψ
    have hker : x ∈ ψ.ker.map D.subtype := by
      refine (Subgroup.closure_le (ψ.ker.map D.subtype)).mpr ?_ hx
      rintro y ⟨hyD, k, hk⟩
      refine ⟨⟨y, hyD⟩, ?_, rfl⟩
      show ψ ⟨y, hyD⟩ = 1
      apply eq_one_of_pow_two_pow_eq_one hodd (k := k)
      rw [← map_pow]
      have : (⟨y, hyD⟩ : D) ^ 2 ^ k = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hk, pow_orderOf_eq_one]
        rfl
      rw [this, map_one]
    obtain ⟨z, hz, rfl⟩ := hker
    have hzA : (z : GL (Fin n) K) ∈ Ã := hxA
    show entry (z : GL (Fin n) K) i i = 1
    have hz' : (blockOf J ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).det = 1 := hz
    rw [det_blockOf_of_isDiag J (hdiag _ hzA)] at hz'
    have hprod : ∏ j ∈ J, entry (z : GL (Fin n) K) j j =
        (entry (z : GL (Fin n) K) i i) ^ J.card := by
      rw [← Finset.prod_const]
      refine Finset.prod_congr rfl fun j hj => ?_
      exact (mem_blk.mp hj) _ hzA
    have hz'' : (entry (z : GL (Fin n) K) i i) ^ J.card = 1 := by rw [← hprod]; exact hz'
    have hcard1 : 1 ≤ J.card := Finset.card_pos.mpr ⟨i, mem_blk.mpr fun a _ => rfl⟩
    have hcard2 : J.card < p := by
      obtain ⟨a, ha, i₀, j₀, hne⟩ := hnot
      have hJne : J ≠ Finset.univ := by
        intro hJu
        have h1 := mem_blk.mp (hJu ▸ Finset.mem_univ i₀ : i₀ ∈ J) a ha
        have h2 := mem_blk.mp (hJu ▸ Finset.mem_univ j₀ : j₀ ∈ J) a ha
        exact hne (h1.trans h2.symm)
      have : J.card < (Finset.univ : Finset (Fin n)).card :=
        Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hJne)
      rw [Finset.card_univ, Fintype.card_fin] at this
      omega
    have hcop : Nat.gcd J.card p = 1 := by
      have : ¬ p ∣ J.card := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
      exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr this)
    have hxp : (entry (z : GL (Fin n) K) i i) ^ p = 1 := by
      have h1 := hexp _ hzA
      have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i i) h1
      simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
      rw [entry_pow_of_isDiag (hdiag _ hzA)] at h2
      simpa using h2
    have h3 := pow_gcd_eq_one.mpr ⟨hz'', hxp⟩
    rwa [hcop, pow_one] at h3
  apply Units.ext
  rw [← (hdiag x hxA).diagonal_diag]
  have : (x : Matrix (Fin n) (Fin n) K).diag = fun _ => 1 := funext hxi
  rw [this]
  simp

theorem exists_entry_ne_of_card_gt {p : ℕ} (hp : 0 < p) (hn : 0 < n)
    (Ã : Subgroup (GL (Fin n) K))
    (hdiag : ∀ a ∈ Ã, ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    (hexp : ∀ a ∈ Ã, a ^ p = 1) (hcard : p < Nat.card Ã) :
    ∃ a ∈ Ã, ∃ i j : Fin n, entry a i i ≠ entry a j j := by
  classical
  by_contra hcon
  push Not at hcon
  set i₀ : Fin n := ⟨0, hn⟩ with hi₀
  have hroot : ∀ a : Ã,
      (entry (a : GL (Fin n) K) i₀ i₀) ∈ (Polynomial.nthRoots p (1 : K)).toFinset := by
    intro a
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hp]
    have h1 := hexp _ a.2
    have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) i₀ i₀) h1
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
    rw [entry_pow_of_isDiag (hdiag _ a.2)] at h2
    simpa using h2
  let f : Ã → (Polynomial.nthRoots p (1 : K)).toFinset := fun a => ⟨_, hroot a⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : entry (a : GL (Fin n) K) i₀ i₀ = entry (b : GL (Fin n) K) i₀ i₀ :=
      congrArg Subtype.val hab
    apply Subtype.ext
    apply Units.ext
    ext r s
    by_cases hrs : r = s
    · subst hrs
      show entry (a : GL (Fin n) K) r r = entry (b : GL (Fin n) K) r r
      rw [hcon a a.2 r i₀, hcon b b.2 r i₀]
      exact hab'
    · rw [(hdiag _ a.2) hrs, (hdiag _ b.2) hrs]
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := ↥(Polynomial.nthRoots p (1 : K)).toFinset),
    Fintype.card_coe] at h1
  have h2 := Multiset.toFinset_card_le (Polynomial.nthRoots p (1 : K))
  have h3 := Polynomial.card_nthRoots p (1 : K)
  omega

end Centralizer

end CFSG.RankThree.PartOne.KFSU5
