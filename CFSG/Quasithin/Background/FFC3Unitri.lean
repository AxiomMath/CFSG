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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin

namespace FFC

open Matrix

@[expose] def UT (n : ℕ) : Subgroup (GL (Fin n) (ZMod 2)) where
  carrier := {g | ∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) (ZMod 2)) i j = 0}
  mul_mem' := by
    intro a b ha hb
    have h : ((a * b : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).BlockTriangular id := by
      rw [Units.val_mul]
      exact Matrix.BlockTriangular.mul (fun i j hij => ha i j hij) (fun i j hij => hb i j hij)
    exact fun i j hij => h hij
  one_mem' := by
    intro i j hij
    simp [ne_of_gt hij]
  inv_mem' := by
    intro a ha
    have : Invertible (a : Matrix (Fin n) (Fin n) (ZMod 2)) := a.invertible
    have h := Matrix.blockTriangular_inv_of_blockTriangular (M := (a : Matrix (Fin n) (Fin n) (ZMod 2))) (b := id) (fun i j hij => ha i j hij)
    intro i j hij
    show ((a⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) i j = 0
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact h hij

theorem mem_UT {n : ℕ} {g : GL (Fin n) (ZMod 2)} :
    g ∈ UT n ↔ ∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) (ZMod 2)) i j = 0 := Iff.rfl

theorem UT_diag {n : ℕ} {g : GL (Fin n) (ZMod 2)} (hg : g ∈ UT n) (i : Fin n) :
    (g : Matrix (Fin n) (Fin n) (ZMod 2)) i i = 1 := by
  have hdet : (g : Matrix (Fin n) (Fin n) (ZMod 2)).det = ∏ k, (g : Matrix (Fin n) (Fin n) (ZMod 2)) k k :=
    Matrix.det_of_isUpperTriangular (fun i j hij => hg i j hij)
  have hu : IsUnit (g : Matrix (Fin n) (Fin n) (ZMod 2)).det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  rw [hdet] at hu
  have h1 : IsUnit ((g : Matrix (Fin n) (Fin n) (ZMod 2)) i i) :=
    (IsUnit.prod_iff ).1 hu i (Finset.mem_univ i)
  have h2 : ∀ x : ZMod 2, IsUnit x → x = 1 := by decide
  exact h2 _ h1

theorem card_pairs_lt (n : ℕ) :
    Fintype.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  classical
  rw [Fintype.card_subtype]
  have h1 : ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2)).card
      = ∑ i : Fin n, (Finset.Ioi i).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.card_filter]
    congr 1
    ext j
    simp
  rw [h1]
  simp only [Fin.card_Ioi]
  have h2 : ∑ i : Fin n, (n - 1 - (i : ℕ)) = ∑ i ∈ Finset.range n, (n - 1 - i) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n]
  rw [h2, Finset.sum_range_reflect (fun i => i) n]
  have := Finset.sum_range_id_mul_two n
  omega

@[expose] def strictUpperMat (n : ℕ) (f : {p : Fin n × Fin n // p.1 < p.2} → ZMod 2) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else 0

theorem det_one_add_strictUpperMat (n : ℕ) (f : {p : Fin n × Fin n // p.1 < p.2} → ZMod 2) :
    (1 + strictUpperMat n f).det = 1 := by
  have hT : (1 + strictUpperMat n f).IsUpperTriangular := by
    intro i j hij
    have h1 : ¬ i < j := not_lt.2 hij.le
    have h2 : i ≠ j := ne_of_gt hij
    simp [strictUpperMat, h1, h2]
  rw [Matrix.det_of_isUpperTriangular hT]
  refine Finset.prod_eq_one fun i _ => ?_
  simp [strictUpperMat]

@[expose] noncomputable def utOfPairs (n : ℕ) (f : {p : Fin n × Fin n // p.1 < p.2} → ZMod 2) :
    GL (Fin n) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mk'' (1 + strictUpperMat n f)
    (by rw [det_one_add_strictUpperMat]; exact isUnit_one)

theorem utOfPairs_val (n : ℕ) (f : {p : Fin n × Fin n // p.1 < p.2} → ZMod 2) :
    (utOfPairs n f : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 + strictUpperMat n f := rfl

theorem utOfPairs_mem (n : ℕ) (f : {p : Fin n × Fin n // p.1 < p.2} → ZMod 2) :
    utOfPairs n f ∈ UT n := by
  intro i j hij
  have h1 : ¬ i < j := not_lt.2 hij.le
  have h2 : i ≠ j := ne_of_gt hij
  simp [utOfPairs_val, strictUpperMat, h1, h2]

@[expose] noncomputable def utEquiv (n : ℕ) : UT n ≃ ({p : Fin n × Fin n // p.1 < p.2} → ZMod 2) where
  toFun g := fun p => (g.1 : Matrix (Fin n) (Fin n) (ZMod 2)) p.1.1 p.1.2
  invFun f := ⟨utOfPairs n f, utOfPairs_mem n f⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [utOfPairs_val]
    rcases lt_trichotomy i j with h | h | h
    · simp [strictUpperMat, h, ne_of_lt h]
    · subst h
      simp [strictUpperMat, UT_diag g.2 i]
    · have := g.2 i j h
      simp [strictUpperMat, not_lt.2 h.le, ne_of_gt h, this]
  right_inv f := by
    funext p
    show (utOfPairs n f : Matrix (Fin n) (Fin n) (ZMod 2)) p.1.1 p.1.2 = f p
    rw [utOfPairs_val]
    have h := p.2
    simp [strictUpperMat, h, ne_of_lt h]

theorem card_UT (n : ℕ) : Nat.card (UT n) = 2 ^ (n * (n - 1) / 2) := by
  rw [Nat.card_congr (utEquiv n), Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
    card_pairs_lt]


theorem card_GL_two (n : ℕ) :
    Nat.card (GL (Fin n) (ZMod 2)) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  rw [Matrix.card_GL_field, ZMod.card]

theorem two_pow_sub_one_odd {k : ℕ} (hk : 1 ≤ k) : ¬ 2 ∣ 2 ^ k - 1 := by
  have h1 : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  omega

theorem index_UT_odd (n : ℕ) : ¬ 2 ∣ (UT n).index := by
  have h := (UT n).index_mul_card
  rw [card_UT, card_GL_two] at h
  have hf : ∀ i : Fin n, 2 ^ n - 2 ^ (i : ℕ) = 2 ^ (i : ℕ) * (2 ^ (n - (i : ℕ)) - 1) := by
    intro i
    have hi : (i : ℕ) ≤ n := i.2.le
    have : 2 ^ n = 2 ^ (i : ℕ) * 2 ^ (n - (i : ℕ)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [Nat.mul_sub, mul_one, ← this]
  simp_rw [hf] at h
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] at h
  have hs : ∑ i : Fin n, (i : ℕ) = n * (n - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) n]
    have := Finset.sum_range_id_mul_two n
    omega
  rw [hs] at h
  have h' : (UT n).index = ∏ i : Fin n, (2 ^ (n - (i : ℕ)) - 1) := by
    have hpos : 0 < 2 ^ (n * (n - 1) / 2) := by positivity
    have : (UT n).index * 2 ^ (n * (n - 1) / 2) = (∏ i : Fin n, (2 ^ (n - (i : ℕ)) - 1)) * 2 ^ (n * (n - 1) / 2) := by
      rw [h, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [h']
  intro hdvd
  rw [Prime.dvd_finsetProd_iff Nat.prime_two.prime] at hdvd
  obtain ⟨i, -, hi⟩ := hdvd
  exact two_pow_sub_one_odd (by have := i.2; omega) hi


theorem isPGroup_UT (n : ℕ) : IsPGroup 2 (UT n) := IsPGroup.of_card (card_UT n)

@[expose] noncomputable def UTSylow (n : ℕ) : Sylow 2 (GL (Fin n) (ZMod 2)) :=
  (isPGroup_UT n).toSylow (index_UT_odd n)

theorem coe_UTSylow (n : ℕ) : ((UTSylow n : Sylow 2 (GL (Fin n) (ZMod 2))) : Subgroup _) = UT n := rfl

theorem exists_conj_UT {n : ℕ} {T : Subgroup (GL (Fin n) (ZMod 2))} (hT : IsPGroup 2 T)
    (hi : ¬ 2 ∣ T.index) : ∃ h : GL (Fin n) (ZMod 2), ∀ x, x ∈ T ↔ h⁻¹ * x * h ∈ UT n := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL (Fin n) (ZMod 2)) (UTSylow n) (hT.toSylow hi)
  refine ⟨g, fun x => ?_⟩
  have h1 : (hT.toSylow hi : Subgroup (GL (Fin n) (ZMod 2))) = T := rfl
  rw [← h1, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rfl


@[expose] noncomputable def permGL {m : ℕ} (σ : Equiv.Perm (Fin m)) : GL (Fin m) (ZMod 2) :=
  MonoidHom.toHomUnits (Matrix.permMatrixHom (n := Fin m) (R := ZMod 2)) σ

theorem permGL_val {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    ((permGL σ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) =
      (σ⁻¹).permMatrix (ZMod 2) := by
  simp [permGL]

theorem permGL_conj_apply {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : GL (Fin m) (ZMod 2))
    (a b : Fin m) :
    ((permGL σ * x * (permGL σ)⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) a b
      = (x : Matrix (Fin m) (Fin m) (ZMod 2)) (σ⁻¹ a) (σ⁻¹ b) := by
  have h : (permGL σ)⁻¹ = permGL σ⁻¹ :=
    (map_inv (MonoidHom.toHomUnits (Matrix.permMatrixHom (n := Fin m) (R := ZMod 2))) σ).symm
  rw [h, Units.val_mul, Units.val_mul, permGL_val, permGL_val]
  simp [Equiv.Perm.permMatrix, Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.symm_apply_eq]
  have e1 : ∀ x₁, (σ x₁ = b) ↔ (x₁ = σ.symm b) := fun x₁ => (Equiv.eq_symm_apply σ).symm
  have e2 : ∀ x₂, (a = σ x₂) ↔ (σ.symm a = x₂) := fun x₂ => (Equiv.symm_apply_eq σ).symm
  simp only [e1, e2, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem eq_bot_of_normal_isPGroup {m : ℕ} {N : Subgroup (GL (Fin m) (ZMod 2))} [N.Normal]
    (hN : IsPGroup 2 N) : N = ⊥ := by
  have hle : N ≤ UT m := IsPGroup.le_sylow_of_normal hN (UTSylow m)
  rw [eq_bot_iff]
  intro x hx
  have hxU : x ∈ UT m := hle hx
  rw [Subgroup.mem_bot]
  apply Units.ext
  ext i j
  rcases lt_trichotomy i j with h | h | h
  ·
    have hy : permGL (Equiv.swap i j) * x * (permGL (Equiv.swap i j))⁻¹ ∈ UT m :=
      hle (Subgroup.Normal.conj_mem inferInstance x hx _)
    have h1 := hy j i h
    rw [permGL_conj_apply] at h1
    have h2 : (Equiv.swap i j)⁻¹ j = i := by simp
    have h3 : (Equiv.swap i j)⁻¹ i = j := by simp
    rw [h2, h3] at h1
    simp [h1, ne_of_lt h]
  · subst h
    simp [UT_diag hxU i]
  · simp [hxU i j h, ne_of_gt h]


@[expose] noncomputable def elemTv {n : ℕ} (i j : Fin n) (h : i ≠ j) : GL (Fin n) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.transvection i j 1)
    (by rw [Matrix.det_transvection_of_ne i j h]; exact isUnit_one)

theorem elemTv_val {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    ((elemTv i j h : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      1 + Matrix.single i j 1 := rfl

theorem elemTv_apply {n : ℕ} (i j : Fin n) (h : i ≠ j) (k l : Fin n) :
    ((elemTv i j h : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) k l =
      (if k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) := by
  rw [elemTv_val]
  simp [Matrix.one_apply, Matrix.single_apply]

theorem elemTv_mulVec {n : ℕ} (i j : Fin n) (h : i ≠ j) (v : Fin n → ZMod 2) (k : Fin n) :
    ((elemTv i j h : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).mulVec v k =
      v k + (if i = k then v j else 0) := by
  simp only [Matrix.mulVec, dotProduct, elemTv_apply, add_mul, Finset.sum_add_distrib]
  simp [ite_and]

theorem elemTv_transpose_mulVec {n : ℕ} (i j : Fin n) (h : i ≠ j) (w : Fin n → ZMod 2) (k : Fin n) :
    ((elemTv i j h : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ.mulVec w k =
      w k + (if j = k then w i else 0) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, elemTv_apply, add_mul,
    Finset.sum_add_distrib]
  simp [ite_and]

theorem elemTv_mem_UT {n : ℕ} {i j : Fin n} (h : i < j) : elemTv i j (ne_of_lt h) ∈ UT n := by
  intro k l hkl
  rw [elemTv_apply]
  have h1 : k ≠ l := ne_of_gt hkl
  have h2 : ¬ (i = k ∧ j = l) := fun ⟨e1, e2⟩ => by
    subst e1; subst e2; exact lt_asymm h hkl
  simp [h1, h2]

theorem fixed_UT_nat {m : ℕ} (v : Fin (m + 1) → ZMod 2) :
    (∀ g ∈ UT (m + 1), (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)).mulVec v = v) ↔
      ∀ j : Fin (m + 1), j ≠ 0 → v j = 0 := by
  constructor
  · intro h j hj
    have hlt : (0 : Fin (m + 1)) < j := Fin.pos_iff_ne_zero.2 hj
    have h1 := congrFun (h _ (elemTv_mem_UT hlt)) 0
    rw [elemTv_mulVec] at h1
    simpa using h1
  · intro h g hg
    funext k
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single (0 : Fin (m + 1))]
    · by_cases hk : k = 0
      · subst hk
        rw [UT_diag hg 0, one_mul]
      · rw [hg k 0 (Fin.pos_iff_ne_zero.2 hk), zero_mul, h k hk]
    · intro l _ hl
      rw [h l hl, mul_zero]
    · intro h0
      exact absurd (Finset.mem_univ _) h0

theorem fixed_UT_dual {m : ℕ} (w : Fin (m + 1) → ZMod 2) :
    (∀ g ∈ UT (m + 1), ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2))ᵀ).mulVec w = w) ↔
      ∀ j : Fin (m + 1), j ≠ Fin.last m → w j = 0 := by
  constructor
  · intro h j hj
    have hlt : j < Fin.last m := lt_of_le_of_ne (Fin.le_last j) hj
    have h1 := congrFun (h _ (elemTv_mem_UT hlt)) (Fin.last m)
    rw [elemTv_transpose_mulVec] at h1
    simpa using h1
  · intro h g hg
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Finset.sum_eq_single (Fin.last m)]
    · by_cases hk : k = Fin.last m
      · subst hk
        rw [UT_diag hg _, one_mul]
      · rw [hg (Fin.last m) k (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul, h k hk]
    · intro l _ hl
      rw [h l hl, mul_zero]
    · intro h0
      exact absurd (Finset.mem_univ _) h0


end FFC

end CFSG.Quasithin
