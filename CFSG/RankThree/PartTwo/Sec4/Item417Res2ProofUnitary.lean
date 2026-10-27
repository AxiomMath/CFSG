module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417Frame

open Matrix

variable {K : Type} [Field K]

@[expose] def fixSub (P : Subgroup (GL (Fin 3) K)) : Submodule K (Fin 3 → K) where
  carrier := {v | ∀ M ∈ P, (M : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v}
  add_mem' := by
    intro v w hv hw M hM
    rw [Matrix.mulVec_add, hv M hM, hw M hM]
  zero_mem' := by
    intro M _
    exact Matrix.mulVec_zero _
  smul_mem' := by
    intro c v hv M hM
    rw [Matrix.mulVec_smul, hv M hM]

theorem mulVec_mem_fixSub {P : Subgroup (GL (Fin 3) K)} {D : GL (Fin 3) K}
    (hDP : ∀ M ∈ P, D⁻¹ * M * D ∈ P) {v : Fin 3 → K} (hv : v ∈ fixSub P) :
    (D : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ fixSub P := by
  intro M hM
  have h := hv _ (hDP M hM)
  have e : (M : Matrix (Fin 3) (Fin 3) K) * D =
      D * ((D⁻¹ * M * D : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, h]

theorem single_mem_fixSub {P : Subgroup (GL (Fin 3) K)} {D : GL (Fin 3) K} {d : Fin 3 → K}
    (hD : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d) (hd : Function.Injective d)
    (hDP : ∀ M ∈ P, D⁻¹ * M * D ∈ P) {v : Fin 3 → K} (hv : v ∈ fixSub P) (i : Fin 3) :
    Pi.single i (v i) ∈ fixSub P := by
  classical
  obtain ⟨j, k, hij, hik, hall⟩ : ∃ j k : Fin 3, i ≠ j ∧ i ≠ k ∧
      ∀ l : Fin 3, l = i ∨ l = j ∨ l = k := by
    fin_cases i
    · exact ⟨1, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 2, by decide, by decide, by decide⟩
    · exact ⟨0, 1, by decide, by decide, by decide⟩
  have hv1 := mulVec_mem_fixSub hDP hv
  have hv2 := mulVec_mem_fixSub hDP hv1
  set w : Fin 3 → K := (D : Matrix (Fin 3) (Fin 3) K) *ᵥ ((D : Matrix (Fin 3) (Fin 3) K) *ᵥ v) -
    (d j + d k) • ((D : Matrix (Fin 3) (Fin 3) K) *ᵥ v) + (d j * d k) • v with hw
  have hwmem : w ∈ fixSub P :=
    add_mem (sub_mem hv2 (Submodule.smul_mem _ _ hv1)) (Submodule.smul_mem _ _ hv)
  have hc : (d i - d j) * (d i - d k) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr fun h => hij (hd h)) (sub_ne_zero.mpr fun h => hik (hd h))
  have hwe : w = Pi.single i ((d i - d j) * (d i - d k) * v i) := by
    funext l
    simp only [hw, hD, Matrix.mulVec_diagonal, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rcases hall l with rfl | rfl | rfl
    · rw [Pi.single_eq_same]
      ring
    · rw [Pi.single_eq_of_ne (Ne.symm hij)]
      ring
    · rw [Pi.single_eq_of_ne (Ne.symm hik)]
      ring
  have : Pi.single i (v i) = ((d i - d j) * (d i - d k))⁻¹ • w := by
    rw [hwe, ← Pi.single_smul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [this]
  exact Submodule.smul_mem _ _ hwmem

theorem apply_eq_zero_of_unitary {σ : K →+* K} {γ : Fin 3 → K} (hγ : ∀ i, γ i ≠ 0)
    {M : Matrix (Fin 3) (Fin 3) K} (hM : (M.map σ)ᵀ * diagonal γ * M = diagonal γ) {i : Fin 3}
    (hi : M *ᵥ Pi.single i 1 = Pi.single i 1) {j : Fin 3} (hij : i ≠ j) : M i j = 0 := by
  classical
  have hcol : ∀ l, M l i = (Pi.single i (1 : K) : Fin 3 → K) l := fun l => by
    rw [← hi, Matrix.mulVec_single_one]
    rfl
  have h := congrFun (congrFun hM i) j
  rw [Matrix.mul_apply, Matrix.diagonal_apply_ne _ hij] at h
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply, hcol] at h
  rw [Finset.sum_eq_single i] at h
  · rw [Pi.single_eq_same, map_one, one_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (hγ i)
  · intro l _ hl
    rw [Pi.single_eq_of_ne hl, map_zero, zero_mul, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem eq_bot_of_unitary [Finite K] (h2 : (2 : K) = 0) {σ : K →+* K} {γ : Fin 3 → K}
    (hγ : ∀ i, γ i ≠ 0) {P : Subgroup (GL (Fin 3) K)} (hP : IsPGroup 2 P)
    (hPu : ∀ M ∈ P, ((M : Matrix (Fin 3) (Fin 3) K).map σ)ᵀ * diagonal γ * M = diagonal γ)
    {D : GL (Fin 3) K} {d : Fin 3 → K} (hD : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d)
    (hd : Function.Injective d) (hDP : ∀ M ∈ P, D⁻¹ * M * D ∈ P) : P = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hall : ∀ i : Fin 3, Pi.single i (1 : K) ∈ fixSub P := by
    by_contra hne
    push Not at hne
    obtain ⟨l₀, hl₀⟩ := hne
    set S : Set (Fin 3) := {i | Pi.single i (1 : K) ∈ fixSub P} with hS
    let W : Submodule K (Fin 3 → K) :=
      { carrier := {v | ∀ i ∈ S, v i = 0}
        add_mem' := by
          intro v w hv hw i hi
          rw [Pi.add_apply, hv i hi, hw i hi, add_zero]
        zero_mem' := fun _ _ => rfl
        smul_mem' := by
          intro c v hv i hi
          rw [Pi.smul_apply, hv i hi, smul_zero] }
    have hWinv : ∀ M ∈ P, ∀ v ∈ W, (M : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
      intro M hM v hv i hi
      have hrow : ∀ j, i ≠ j → (M : Matrix (Fin 3) (Fin 3) K) i j = 0 :=
        fun j hij => apply_eq_zero_of_unitary hγ (hPu M hM) (hi M hM) hij
      change ((M : Matrix (Fin 3) (Fin 3) K) *ᵥ v) i = 0
      rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
      · rw [hv i hi, mul_zero]
      · intro j _ hj
        rw [hrow j (Ne.symm hj), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    let _ : MulAction P W :=
      { smul := fun M w =>
          ⟨((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K),
            hWinv M M.2 w w.2⟩
        one_smul := fun w => Subtype.ext (by
          change (((1 : P) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K) = w
          rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec])
        mul_smul := fun M N w => Subtype.ext (by
          change (((M * N : P) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            (w : Fin 3 → K) = ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
              (((N : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (w : Fin 3 → K))
          rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]) }
    have hx : (Pi.single l₀ (1 : K) : Fin 3 → K) ∈ W := by
      intro i hi
      have : i ≠ l₀ := fun h => hl₀ (h ▸ hi)
      exact Pi.single_eq_of_ne this 1
    have h2W : 2 ∣ Nat.card W := by
      have hord : addOrderOf (⟨(Pi.single l₀ (1 : K) : Fin 3 → K), hx⟩ : W) = 2 := by
        apply addOrderOf_eq_prime
        · apply Subtype.ext
          funext l
          change (2 • (Pi.single l₀ (1 : K) : Fin 3 → K)) l = 0
          rw [Pi.smul_apply, two_nsmul, ← two_mul, h2, zero_mul]
        · intro h
          have := congrArg (fun w : W => (w : Fin 3 → K) l₀) h
          simp only [Pi.single_eq_same] at this
          exact one_ne_zero this
      rw [← hord]
      exact addOrderOf_dvd_natCard _
    have h0 : (0 : W) ∈ MulAction.fixedPoints P W := by
      intro M
      apply Subtype.ext
      change ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ (0 : Fin 3 → K) = 0
      exact Matrix.mulVec_zero _
    obtain ⟨w, hw, hw0⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point W h2W h0
    have hwfix : (w : Fin 3 → K) ∈ fixSub P := by
      intro M hM
      exact congrArg Subtype.val (hw ⟨M, hM⟩)
    obtain ⟨m, hm⟩ : ∃ m, (w : Fin 3 → K) m ≠ 0 := by
      by_contra h
      push Not at h
      exact hw0 (Subtype.ext (funext fun l => (h l).symm))
    have hmS : m ∉ S := fun hmS => hm (w.2 m hmS)
    apply hmS
    have h1 := single_mem_fixSub hD hd hDP hwfix m
    have : Pi.single m (1 : K) = ((w : Fin 3 → K) m)⁻¹ • Pi.single m ((w : Fin 3 → K) m) := by
      rw [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hm]
    change Pi.single m (1 : K) ∈ fixSub P
    rw [this]
    exact Submodule.smul_mem _ _ h1
  rw [eq_bot_iff]
  intro M hM
  rw [Subgroup.mem_bot]
  apply Units.ext
  ext r i
  have := congrFun (hall i M hM) r
  rw [Matrix.mulVec_single_one] at this
  rw [Units.val_one, Matrix.one_apply]
  change (M : Matrix (Fin 3) (Fin 3) K) r i = (Pi.single i (1 : K) : Fin 3 → K) r at this
  rw [this, Pi.single_apply]

@[expose] def frameMat (b : Fin 3 → (Fin 3 → K)) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun r i => b i r

theorem mul_frameMat_eq {y : Matrix (Fin 3) (Fin 3) K} {b : Fin 3 → (Fin 3 → K)}
    {d : Fin 3 → K} (h : ∀ i, y *ᵥ b i = d i • b i) :
    y * frameMat b = frameMat b * diagonal d := by
  ext r i
  have hi := congrFun (h i) r
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hi
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, frameMat, of_apply]
  rw [hi, mul_comm]

theorem isUnit_frameMat {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b) :
    IsUnit (frameMat b) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  convert hb using 1
  funext i r
  rfl

theorem mul_ne_one_of_ne {σ : K →+* K} (hσσ : ∀ x, σ (σ x) = x)
    (hσρ : ∀ ρ : K, ρ ^ 3 = 1 → σ ρ * ρ = 1) {d : Fin 3 → K} (hd : Function.Injective d)
    (hd0 : ∀ i, d i ≠ 0) (hd3 : ∀ i j, d i ^ 3 = d j ^ 3) {i j : Fin 3} (hij : i ≠ j) :
    σ (d i) * d j ≠ 1 := by
  intro h
  have hdi := hd0 i
  set ρ := d j / d i with hρ
  have hρ3 : ρ ^ 3 = 1 := by rw [hρ, div_pow, hd3 j i, div_self (pow_ne_zero 3 hdi)]
  have hρ1 : ρ ≠ 1 := fun h1 => hij (hd ((div_eq_one_iff_eq hdi).mp h1).symm)
  have hN : σ (d i) * d i * ρ = 1 := by
    rw [hρ, mul_assoc, mul_div_cancel₀ _ hdi]
    exact h
  have hσN : σ (σ (d i) * d i) = σ (d i) * d i := by rw [map_mul, hσσ, mul_comm]
  have h1 : σ (σ (d i) * d i * ρ) = 1 := by rw [hN, map_one]
  rw [map_mul, hσN] at h1
  have hN0 : σ (d i) * d i ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hN
    exact zero_ne_one hN
  have hσρρ : σ ρ = ρ := mul_left_cancel₀ hN0 (h1.trans hN.symm)
  have hρρ := hσρ ρ hρ3
  rw [hσρρ] at hρρ
  apply hρ1
  calc ρ = ρ * (ρ * ρ) := by rw [hρρ, mul_one]
    _ = ρ ^ 3 := by ring
    _ = 1 := hρ3

theorem eq_bot_of_unitary_eigen [Finite K] (h2 : (2 : K) = 0) {σ : K →+* K}
    (hσσ : ∀ x, σ (σ x) = x) (hσρ : ∀ ρ : K, ρ ^ 3 = 1 → σ ρ * ρ = 1)
    {P : Subgroup (GL (Fin 3) K)} (hP : IsPGroup 2 P)
    (hPu : ∀ M ∈ P, ((M : Matrix (Fin 3) (Fin 3) K).map σ)ᵀ * M = 1)
    {y : GL (Fin 3) K} (hy : ((y : Matrix (Fin 3) (Fin 3) K).map σ)ᵀ * y = 1)
    {b : Fin 3 → (Fin 3 → K)} (hb : LinearIndependent K b) {d : Fin 3 → K}
    (hd : Function.Injective d) (hd3 : ∀ i j, d i ^ 3 = d j ^ 3)
    (hyb : ∀ i, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = d i • b i)
    (hyP : ∀ M ∈ P, y⁻¹ * M * y ∈ P) : P = ⊥ := by
  classical
  set g : GL (Fin 3) K := (isUnit_frameMat hb).unit with hgdef
  have hgm : (g : Matrix (Fin 3) (Fin 3) K) = frameMat b := rfl
  have hyg : (y : Matrix (Fin 3) (Fin 3) K) * g = g * diagonal d := by
    rw [hgm]
    exact mul_frameMat_eq hyb
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i h0
    have h := hyb i
    rw [h0, zero_smul] at h
    have hinj := (Matrix.mulVec_injective_iff_isUnit (A := (y : Matrix (Fin 3) (Fin 3) K))).mpr
      y.isUnit
    exact hb.ne_zero i (hinj (by rw [h, Matrix.mulVec_zero]))
  set Gm : Matrix (Fin 3) (Fin 3) K := ((g : Matrix (Fin 3) (Fin 3) K).map σ)ᵀ * g with hGm
  have hGrel : Gm = diagonal (fun i => σ (d i)) * Gm * diagonal d := by
    have e1 : Gm = (((y : Matrix (Fin 3) (Fin 3) K) * g).map σ)ᵀ *
        ((y : Matrix (Fin 3) (Fin 3) K) * g) := by
      rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ (g :
        Matrix (Fin 3) (Fin 3) K), hy, Matrix.one_mul]
    calc Gm = _ := e1
      _ = diagonal (fun i => σ (d i)) * Gm * diagonal d := by
        rw [hyg, Matrix.map_mul, Matrix.transpose_mul, Matrix.diagonal_map (map_zero σ),
          Matrix.diagonal_transpose, hGm]
        simp only [Matrix.mul_assoc]
  have hGoff : ∀ i j, i ≠ j → Gm i j = 0 := by
    intro i j hij
    have h := congrFun (congrFun hGrel i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have h' : Gm i j * (σ (d i) * d j - 1) = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_right
      (sub_ne_zero.mpr (mul_ne_one_of_ne hσσ hσρ hd hd0 hd3 hij))
  have hGdiag : Gm = diagonal fun i => Gm i i := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, hGoff i j hij]
  have hGii : ∀ i, Gm i i ≠ 0 := by
    have hdet : Gm.det ≠ 0 := by
      rw [hGm, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      have hg0 : (g : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
        (g.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
      exact mul_ne_zero ((map_ne_zero σ).mpr hg0) hg0
    rw [hGdiag, Matrix.det_diagonal] at hdet
    exact fun i => Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
  set P' : Subgroup (GL (Fin 3) K) := P.comap (MulAut.conj g).toMonoidHom with hP'
  have hmemP' : ∀ M, M ∈ P' ↔ g * M * g⁻¹ ∈ P := fun M => Iff.rfl
  have hP'p : IsPGroup 2 P' := hP.comap_of_injective _ (MulAut.conj g).injective
  have hginv : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * g = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hginv' : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hP'u : ∀ M ∈ P', ((M : Matrix (Fin 3) (Fin 3) K).map σ)ᵀ *
      diagonal (fun i => Gm i i) * M = diagonal fun i => Gm i i := by
    intro M hM
    rw [← hGdiag]
    set N : GL (Fin 3) K := g * M * g⁻¹ with hNdef
    have hN : ((N : Matrix (Fin 3) (Fin 3) K).map σ)ᵀ * N = 1 := hPu N ((hmemP' M).mp hM)
    have hMN : (M : Matrix (Fin 3) (Fin 3) K) = ((g⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) * N * g := by
      rw [← Units.val_mul, ← Units.val_mul, hNdef]
      congr 1
      group
    set A : Matrix (Fin 3) (Fin 3) K := (g : Matrix (Fin 3) (Fin 3) K) with hA
    set Ai : Matrix (Fin 3) (Fin 3) K := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      with hAi
    set Nm : Matrix (Fin 3) (Fin 3) K := (N : Matrix (Fin 3) (Fin 3) K) with hNm
    have hbar : (Ai.map σ)ᵀ * (A.map σ)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hginv', Matrix.map_one _ (map_zero σ)
        (map_one σ), Matrix.transpose_one]
    rw [hMN, hGm]
    simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Ai.map σ)ᵀ (A.map σ)ᵀ, hbar, Matrix.one_mul,
      ← Matrix.mul_assoc A Ai, hginv', Matrix.one_mul, ← Matrix.mul_assoc (Nm.map σ)ᵀ Nm, hN,
      Matrix.one_mul]
  set D : GL (Fin 3) K := g⁻¹ * y * g with hDdef
  have hD : (D : Matrix (Fin 3) (Fin 3) K) = diagonal d := by
    rw [hDdef, Units.val_mul, Units.val_mul, Matrix.mul_assoc, hyg, ← Matrix.mul_assoc, hginv,
      Matrix.one_mul]
  have hDP : ∀ M ∈ P', D⁻¹ * M * D ∈ P' := by
    intro M hM
    rw [hmemP'] at hM ⊢
    have e : g * (D⁻¹ * M * D) * g⁻¹ = y⁻¹ * (g * M * g⁻¹) * y := by
      rw [hDdef]
      group
    rw [e]
    exact hyP _ hM
  have hP'bot := eq_bot_of_unitary h2 hGii hP'p hP'u hD hd hDP
  rw [eq_bot_iff]
  intro M hM
  have hM' : g⁻¹ * M * g ∈ P' := by
    rw [hmemP']
    have : g * (g⁻¹ * M * g) * g⁻¹ = M := by group
    rw [this]
    exact hM
  rw [hP'bot, Subgroup.mem_bot] at hM'
  rw [Subgroup.mem_bot]
  calc M = g * (g⁻¹ * M * g) * g⁻¹ := by group
    _ = 1 := by rw [hM']; group

end CFSG.RankThree.PartTwo.Sec4.Res417Frame
