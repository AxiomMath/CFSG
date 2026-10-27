module

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
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

public section

namespace CFSG.RankThree.PartTwo.Sec19.NF5Pair
open Matrix

variable {F : Type*} [Field F]

@[expose] def IsHeis (g : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∀ (w : Fin 3 → F) (θ : F), w ≠ 0 → g *ᵥ w ≠ θ • w

@[expose] def IsHomol (g : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∃ (a : F) (u v : Fin 3 → F), u ≠ 0 ∧ v ≠ 0 ∧
    g = a • (1 : Matrix (Fin 3) (Fin 3) F) + Matrix.vecMulVec u v

@[expose] def Dm (ω : F) : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![1, ω, ω ^ 2]

@[expose] def IsReg (ω : F) (g : Matrix (Fin 3) (Fin 3) F) : Prop :=
  ∃ (a : Matrix (Fin 3) (Fin 3) F) (μ : F), IsUnit a ∧ g * a = a * (μ • Dm ω)

@[expose] def homMat (ω : F) : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![1, 1, ω]

@[expose] def heisMat (l : F) : Matrix (Fin 3) (Fin 3) F := !![0, 0, l; 1, 0, 0; 0, 1, 0]

@[expose] def Pm : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def Phi (ω : F) : Matrix (Fin 3) (Fin 3) F := !![1, 1, 1; 1, ω, ω ^ 2; 1, ω ^ 2, ω]

section Leaves

theorem IsHeis.conj_smul {g k : Matrix (Fin 3) (Fin 3) F} (hk : IsUnit k) (s : F) (hs : s ≠ 0)
    (h : IsHeis g) : IsHeis (s • (k * g * k⁻¹)) := by
  intro w θ hw hEq
  have hd := (Matrix.isUnit_iff_isUnit_det k).1 hk
  have hkl : k⁻¹ * k = 1 := Matrix.nonsing_inv_mul k hd
  have hlk : k * k⁻¹ = 1 := Matrix.mul_nonsing_inv k hd
  have hk' : ∀ y, k⁻¹ *ᵥ (k *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hkl, Matrix.one_mulVec]
  have hk'' : ∀ y, k *ᵥ (k⁻¹ *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hlk, Matrix.one_mulVec]
  apply h (k⁻¹ *ᵥ w) (θ / s)
  · intro h0
    apply hw
    calc w = k *ᵥ (k⁻¹ *ᵥ w) := (hk'' w).symm
      _ = 0 := by rw [h0, Matrix.mulVec_zero]
  · have h1 : s • (k *ᵥ (g *ᵥ (k⁻¹ *ᵥ w))) = θ • w := by
      rw [← hEq, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have h3 := congrArg (fun y => k⁻¹ *ᵥ y) h1
    simp only [Matrix.mulVec_smul, hk'] at h3
    have h4 : g *ᵥ (k⁻¹ *ᵥ w) = (θ / s) • (k⁻¹ *ᵥ w) := by
      have h5 := congrArg (fun y => s⁻¹ • y) h3
      simp only [smul_smul, inv_mul_cancel₀ hs, one_smul] at h5
      rw [h5]
      congr 1
      field_simp
    exact h4

theorem IsHomol.conj_smul {g k : Matrix (Fin 3) (Fin 3) F} (hk : IsUnit k) (s : F) (hs : s ≠ 0)
    (h : IsHomol g) : IsHomol (s • (k * g * k⁻¹)) := by
  obtain ⟨a, u, v, hu, hv, rfl⟩ := h
  have hd := (Matrix.isUnit_iff_isUnit_det k).1 hk
  have hkl : k⁻¹ * k = 1 := Matrix.nonsing_inv_mul k hd
  have hlk : k * k⁻¹ = 1 := Matrix.mul_nonsing_inv k hd
  have hk' : ∀ y, k⁻¹ *ᵥ (k *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hkl, Matrix.one_mulVec]
  refine ⟨s * a, s • (k *ᵥ u), v ᵥ* k⁻¹, ?_, ?_, ?_⟩
  · intro h0
    apply hu
    have h1 := congrArg (fun y => s⁻¹ • (k⁻¹ *ᵥ y)) h0
    simp only [Matrix.mulVec_smul, hk', smul_smul, inv_mul_cancel₀ hs, one_smul,
      Matrix.mulVec_zero, smul_zero] at h1
    exact h1
  · intro h0
    apply hv
    have h1 := congrArg (fun y => y ᵥ* k) h0
    simpa [Matrix.vecMul_vecMul, hkl, hlk] using h1
  · have e1 : k * (a • (1 : Matrix (Fin 3) (Fin 3) F) + Matrix.vecMulVec u v) * k⁻¹ =
        a • (1 : Matrix (Fin 3) (Fin 3) F) + Matrix.vecMulVec (k *ᵥ u) (v ᵥ* k⁻¹) := by
      rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hlk,
        Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [e1, smul_add, smul_smul, Matrix.smul_vecMulVec]

theorem homMat_spec {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    IsHomol (homMat ω) ∧ IsUnit (homMat ω) ∧ homMat ω ^ 3 = 1 := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨1, (ω - 1) • Pi.single 2 1, Pi.single 2 1, ?_, ?_, ?_⟩
    · intro h0
      have := congrFun h0 2
      simp [sub_eq_zero, hω1] at this
    · intro h0
      have := congrFun h0 2
      simp at this
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [homMat, Matrix.vecMulVec_apply, Pi.single_apply, Matrix.diagonal_apply]
  · rw [Matrix.isUnit_iff_isUnit_det, homMat, Matrix.det_diagonal]
    simp [Fin.prod_univ_three, hω0]
  · rw [homMat, Matrix.diagonal_pow]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, hω3]

theorem heisMat_spec {l : F} (hl : ∀ θ : F, θ ^ 3 ≠ l) :
    IsHeis (heisMat l) ∧ IsUnit (heisMat l) ∧ heisMat l ^ 3 = l • (1 : Matrix (Fin 3) (Fin 3) F) := by
  have hl0 : l ≠ 0 := fun h => hl 0 (by simp [h])
  refine ⟨?_, ?_, ?_⟩
  · intro w θ hw hEq
    have h0 := congrFun hEq 0
    have h1 := congrFun hEq 1
    have h2 := congrFun hEq 2
    simp [heisMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at h0 h1 h2
    by_cases hw2 : w 2 = 0
    · apply hw
      have e1 : w 1 = 0 := by rw [h2, hw2, mul_zero]
      have e0 : w 0 = 0 := by rw [h1, e1, mul_zero]
      ext i
      fin_cases i <;> simp [e0, e1, hw2]
    · apply hl θ
      have : (θ ^ 3 - l) * w 2 = 0 := by
        have e1 : w 0 = θ * (θ * w 2) := by rw [h1, h2]
        linear_combination (-1 : F) * h0 - θ * e1
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hw2)
  · rw [Matrix.isUnit_iff_isUnit_det]
    simp [heisMat, Matrix.det_fin_three, hl0]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [heisMat, pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

theorem exists_noncube [Finite F] {ω : F} (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1) :
    ∃ l : F, ∀ θ : F, θ ^ 3 ≠ l := by
  by_contra h
  have hsurj : Function.Surjective (fun x : F => x ^ 3) := fun l => by
    by_contra h'
    exact h ⟨l, fun θ hθ => h' ⟨θ, hθ⟩⟩
  have hinj := Finite.injective_iff_surjective.2 hsurj
  exact hω1 (hinj (by simp [hω3]))

theorem rank_eq_zero_imp {N : Matrix (Fin 3) (Fin 3) F} (h : N.rank = 0) : N = 0 := by
  have h1 : LinearMap.range N.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h
  ext i j
  have h2 : N *ᵥ (Pi.single j 1) ∈ LinearMap.range N.mulVecLin := ⟨Pi.single j 1, rfl⟩
  rw [h1, Submodule.mem_bot] at h2
  have := congrFun h2 i
  simpa [Matrix.mulVec_single_one] using this

theorem exists_ker_of_rank_lt {N : Matrix (Fin 3) (Fin 3) F} (h : N.rank < 3) :
    ∃ v : Fin 3 → F, v ≠ 0 ∧ N *ᵥ v = 0 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fin_fun] at h1
  have h2 : N.rank = Module.finrank F (LinearMap.range N.mulVecLin) := rfl
  have h3 : 0 < Module.finrank F (LinearMap.ker N.mulVecLin) := by omega
  have hne : LinearMap.ker N.mulVecLin ≠ ⊥ := fun h0 => by
    rw [h0, finrank_bot] at h3
    exact lt_irrefl _ h3
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨v, hv0, hv⟩

theorem rank_le_two_of_ker {N : Matrix (Fin 3) (Fin 3) F} {v : Fin 3 → F} (hv : v ≠ 0)
    (hN : N *ᵥ v = 0) : N.rank ≤ 2 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [Module.finrank_fin_fun] at h1
  have h2 : N.rank = Module.finrank F (LinearMap.range N.mulVecLin) := rfl
  have h3 : 0 < Module.finrank F (LinearMap.ker N.mulVecLin) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨v, hN⟩, fun h0 => hv (congrArg Subtype.val h0)⟩
  omega

theorem rank_one_outer {N : Matrix (Fin 3) (Fin 3) F} (h : N.rank = 1) :
    ∃ u v : Fin 3 → F, u ≠ 0 ∧ v ≠ 0 ∧ N = Matrix.vecMulVec u v := by
  have h1 : Module.finrank F (LinearMap.range N.mulVecLin) = 1 := h
  obtain ⟨e, he0, he⟩ := finrank_eq_one_iff'.1 h1
  have hcol : ∀ j, ∃ c : F, N *ᵥ (Pi.single j 1) = c • (e : Fin 3 → F) := fun j => by
    obtain ⟨c, hc⟩ := he ⟨N *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  choose c hc using hcol
  have he0' : (e : Fin 3 → F) ≠ 0 := fun h0 => he0 (Subtype.ext h0)
  have hN : N = Matrix.vecMulVec (e : Fin 3 → F) c := by
    ext i j
    have := congrFun (hc j) i
    simpa [Matrix.mulVec_single_one, Matrix.vecMulVec_apply, mul_comm] using this
  refine ⟨e, c, he0', ?_, hN⟩
  intro hc0
  rw [hc0] at hN
  have : N = 0 := by rw [hN]; simp
  have h0 : N.rank = 0 := by rw [this]; exact Matrix.rank_zero
  omega

theorem trichotomy (hF2 : (2 : F) = 0) {ω : F} (hω : ω ^ 2 + ω + 1 = 0)
    {g : Matrix (Fin 3) (Fin 3) F} (hg : IsUnit g) {c : F}
    (hg3 : g ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (hns : ∀ μ : F, g ≠ μ • (1 : Matrix (Fin 3) (Fin 3) F)) : IsHeis g ∨ IsHomol g ∨ IsReg ω g := by
  classical
  by_cases hE : IsHeis g
  · exact Or.inl hE
  right
  obtain ⟨w, θ, hw, hgw⟩ : ∃ (w : Fin 3 → F) (θ : F), w ≠ 0 ∧ g *ᵥ w = θ • w := by
    by_contra h
    exact hE fun w θ hw hEq => h ⟨w, θ, hw, hEq⟩
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hg
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    apply hw
    have h1 : g *ᵥ w = 0 := by simpa using hgw
    have := congrArg (fun y => g⁻¹ *ᵥ y) h1
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul g hd] using this
  have hθ3 : θ ^ 3 = c := by
    have e2 : g *ᵥ (g *ᵥ w) = θ ^ 2 • w := by
      rw [hgw, Matrix.mulVec_smul, hgw, smul_smul, pow_two]
    have e3 : g *ᵥ (g *ᵥ (g *ᵥ w)) = θ ^ 3 • w := by
      rw [e2, Matrix.mulVec_smul, hgw, smul_smul, ← pow_succ]
    have h1 : (g ^ 3) *ᵥ w = θ ^ 3 • w := by
      rw [pow_three', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact e3
    rw [hg3, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    by_contra hne
    apply hw
    have h2 : (c - θ ^ 3) • w = 0 := by rw [sub_smul, h1, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have hc0 : c ≠ 0 := by rw [← hθ3]; exact pow_ne_zero 3 hθ0
  set g' : Matrix (Fin 3) (Fin 3) F := θ⁻¹ • g with hg'
  have hg'3 : g' ^ 3 = 1 := by
    have h1 : (θ⁻¹) ^ 3 * c = 1 := by
      rw [← hθ3, ← mul_pow, inv_mul_cancel₀ hθ0, one_pow]
    rw [hg', smul_pow, hg3, smul_smul, h1, one_smul]
  have hg'w : g' *ᵥ w = w := by
    rw [hg', Matrix.smul_mulVec, hgw, smul_smul, inv_mul_cancel₀ hθ0, one_smul]
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hprod : (g' - (1 : Matrix (Fin 3) (Fin 3) F)) * (g' - ω • (1 : Matrix (Fin 3) (Fin 3) F)) *
      (g' - (ω ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F)) = 0 := by
    have hC : Polynomial.C ω ^ 2 + Polynomial.C ω + 1 = 0 := by
      have := congrArg (Polynomial.C : F →+* Polynomial F) hω
      simpa [map_add, map_pow] using this
    have hpoly : (Polynomial.X - Polynomial.C (1 : F)) * (Polynomial.X - Polynomial.C ω) *
        (Polynomial.X - Polynomial.C (ω ^ 2)) = (Polynomial.X ^ 3 - 1 : Polynomial F) := by
      simp only [map_one, map_pow]
      linear_combination (-(Polynomial.X ^ 2) + Polynomial.C ω * Polynomial.X -
        (Polynomial.C ω - 1)) * hC
    have h2 := congrArg (Polynomial.aeval g') hpoly
    simpa [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hg'3,
      Algebra.algebraMap_eq_smul_one, smul_pow] using h2
  have hgg' : g = θ • g' := by rw [hg', smul_smul, mul_inv_cancel₀ hθ0, one_smul]
  have hcomm : ∀ a b : F, (g' - a • (1 : Matrix (Fin 3) (Fin 3) F)) * (g' - b • 1) =
      (g' - b • (1 : Matrix (Fin 3) (Fin 3) F)) * (g' - a • 1) := by
    intro a b
    simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      smul_smul, mul_comm a b]
    abel
  have hprod' : (g' - (1 : F) • (1 : Matrix (Fin 3) (Fin 3) F)) * (g' - ω • 1) *
      (g' - (ω ^ 2) • 1) = 0 := by rw [one_smul]; exact hprod
  have homol_of : ∀ a : F, (g' - a • (1 : Matrix (Fin 3) (Fin 3) F)).rank = 1 → IsHomol g := by
    intro a ha
    obtain ⟨u, v, hu, hv, hNuv⟩ := rank_one_outer ha
    refine ⟨θ * a, θ • u, v, smul_ne_zero hθ0 hu, hv, ?_⟩
    have h1 : g' = a • (1 : Matrix (Fin 3) (Fin 3) F) + Matrix.vecMulVec u v := by
      rw [← hNuv]; abel
    rw [hgg', h1, smul_add, smul_smul, Matrix.smul_vecMulVec]
  have hnz : ∀ a : F, g' - a • (1 : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
    intro a h0
    apply hns (θ * a)
    have : g' = a • (1 : Matrix (Fin 3) (Fin 3) F) := sub_eq_zero.1 h0
    rw [hgg', this, smul_smul]
  have hω1 : ω ≠ 1 := by
    intro h1
    have h3 : (3 : F) = 0 := by rw [h1] at hω; linear_combination hω
    have h4 : (1 : F) = 0 := by linear_combination h3 - hF2
    exact one_ne_zero h4
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have hω2 : ω ^ 2 ≠ 1 := by
    intro h1
    apply hω1
    have h5 : ω ^ 3 = ω := by rw [pow_succ, h1, one_mul]
    rw [← h5, hω3]
  have hω21 : ω ^ 2 ≠ ω := by
    intro h1
    apply hω1
    have : ω * (ω - 1) = 0 := by linear_combination h1
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hω0))
  by_cases hr1 : (g' - (1 : F) • (1 : Matrix (Fin 3) (Fin 3) F)).rank = 1 ∨
      (g' - ω • (1 : Matrix (Fin 3) (Fin 3) F)).rank = 1 ∨
      (g' - (ω ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F)).rank = 1
  · rcases hr1 with h | h | h
    · exact Or.inl (homol_of _ h)
    · exact Or.inl (homol_of _ h)
    · exact Or.inl (homol_of _ h)
  right
  push_neg at hr1
  obtain ⟨hr10, hr11, hr12⟩ := hr1
  set N0 : Matrix (Fin 3) (Fin 3) F := g' - (1 : F) • (1 : Matrix (Fin 3) (Fin 3) F) with hN0
  set N1 : Matrix (Fin 3) (Fin 3) F := g' - ω • (1 : Matrix (Fin 3) (Fin 3) F) with hN1
  set N2 : Matrix (Fin 3) (Fin 3) F := g' - (ω ^ 2) • (1 : Matrix (Fin 3) (Fin 3) F) with hN2
  have hN0w : N0 *ᵥ w = 0 := by
    rw [hN0, Matrix.sub_mulVec, hg'w, Matrix.smul_mulVec, Matrix.one_mulVec, one_smul, sub_self]
  have r0le : N0.rank ≤ 2 := rank_le_two_of_ker hw hN0w
  have r0ge : 2 ≤ N0.rank := by
    have : N0.rank ≠ 0 := fun h => hnz 1 (rank_eq_zero_imp h)
    omega
  have r1ge : 2 ≤ N1.rank := by
    have : N1.rank ≠ 0 := fun h => hnz ω (rank_eq_zero_imp h)
    omega
  have r2ge : 2 ≤ N2.rank := by
    have : N2.rank ≠ 0 := fun h => hnz (ω ^ 2) (rank_eq_zero_imp h)
    omega
  have r1le : N1.rank ≤ 3 := Matrix.rank_le_width N1
  have r2le : N2.rank ≤ 3 := Matrix.rank_le_width N2
  have syl : ∀ {A B : Matrix (Fin 3) (Fin 3) F}, A * B = 0 → A.rank + B.rank ≤ 3 := fun h => by
    simpa using Matrix.rank_add_rank_le_card_of_mul_eq_zero h
  have hN1s : N1.rank < 3 := by
    by_contra hge
    have h3 : N1.rank = 3 := by omega
    have e : N0 * N2 * N1 = 0 := by
      rw [mul_assoc, hcomm (ω ^ 2) ω, ← mul_assoc]; exact hprod'
    have h4 := syl e
    have h5 : N0 * N2 = 0 := rank_eq_zero_imp (by omega)
    have := syl h5
    omega
  have hN2s : N2.rank < 3 := by
    by_contra hge
    have h3 : N2.rank = 3 := by omega
    have h4 := syl hprod'
    have h5 : N0 * N1 = 0 := rank_eq_zero_imp (by omega)
    have := syl h5
    omega
  obtain ⟨v1, hv1, hN1v⟩ := exists_ker_of_rank_lt hN1s
  obtain ⟨v2, hv2, hN2v⟩ := exists_ker_of_rank_lt hN2s
  have hsm : ∀ (a : F) (v : Fin 3 → F),
      (a • (1 : Matrix (Fin 3) (Fin 3) F)) *ᵥ v = a • v := fun a v => by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hg'v1 : g' *ᵥ v1 = ω • v1 := by
    have := hN1v
    rw [hN1, Matrix.sub_mulVec, hsm] at this
    exact sub_eq_zero.1 this
  have hg'v2 : g' *ᵥ v2 = (ω ^ 2) • v2 := by
    have := hN2v
    rw [hN2, Matrix.sub_mulVec, hsm] at this
    exact sub_eq_zero.1 this
  let μ : Fin 3 → F := ![1, ω, ω ^ 2]
  let vv : Fin 3 → (Fin 3 → F) := ![w, v1, v2]
  have h01 : μ 0 ≠ μ 1 := fun h => hω1 h.symm
  have h02 : μ 0 ≠ μ 2 := fun h => hω2 h.symm
  have h12 : μ 1 ≠ μ 2 := fun h => hω21 h.symm
  have hμ : Function.Injective μ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | exact absurd hij h01 | exact absurd hij.symm h01
      | exact absurd hij h02 | exact absurd hij.symm h02
      | exact absurd hij h12 | exact absurd hij.symm h12
  have hli : LinearIndependent F vv := by
    apply Module.End.eigenvectors_linearIndependent' g'.mulVecLin μ hμ vv
    intro i
    fin_cases i
    · exact ⟨Module.End.mem_eigenspace_iff.2 (by simpa [μ, vv] using hg'w), hw⟩
    · exact ⟨Module.End.mem_eigenspace_iff.2 (by simpa [μ, vv] using hg'v1), hv1⟩
    · exact ⟨Module.End.mem_eigenspace_iff.2 (by simpa [μ, vv] using hg'v2), hv2⟩
  set A : Matrix (Fin 3) (Fin 3) F := Matrix.of fun i j => vv j i with hA
  have hAcol : A.col = vv := by
    funext j
    funext i
    rfl
  have hAu : IsUnit A := Matrix.linearIndependent_cols_iff_isUnit.1 (hAcol ▸ hli)
  have hcols : ∀ j, g *ᵥ vv j = (θ * μ j) • vv j := by
    intro j
    rw [hgg', Matrix.smul_mulVec]
    fin_cases j
    · simp only [vv, μ]; simpa [hg'w, smul_smul] using congrArg (fun y => θ • y) hg'w
    · simp only [vv, μ]; simpa [hg'v1, smul_smul] using congrArg (fun y => θ • y) hg'v1
    · simp only [vv, μ]; simpa [hg'v2, smul_smul] using congrArg (fun y => θ • y) hg'v2
  refine ⟨A, θ, hAu, ?_⟩
  ext i j
  have h1 := congrFun (hcols j) i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
  simp only [Matrix.mul_apply, Dm, Matrix.smul_apply, Matrix.diagonal_apply, hA, Matrix.of_apply,
    smul_eq_mul]
  rw [h1]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  show θ * ![1, ω, ω ^ 2] j * vv j i = vv j i * (θ * ![1, ω, ω ^ 2] j)
  ring

theorem fourier_identities (hF2 : (2 : F) = 0) {ω : F} (hω : ω ^ 2 + ω + 1 = 0) :
    Dm ω * Phi ω = Phi ω * Pm ∧ Phi ω * Phi ω * Phi ω * Phi ω = 1 ∧
      Pm * Dm ω = (ω ^ 2) • (Dm ω * Pm) := by
  have h3 : (3 : F) = 1 := by linear_combination hF2
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Dm, Phi, Pm, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;> grind
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Phi, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] <;> grind
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Dm, Pm, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply] <;> grind

end Leaves

end CFSG.RankThree.PartTwo.Sec19.NF5Pair