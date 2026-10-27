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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

open scoped MatrixGroups Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Vec

theorem eq_one_of_cube_smul {F : Type} [Field F] {W : Type} [AddCommGroup W] [Module F W]
    (hcube : ∀ r : F, r ^ 3 = 1 → r = 1) {w : W} (hw : w ≠ 0) {c : F}
    (h : (c * c * c) • w = w) : c = 1 := by
  have h0 : (c * c * c - 1) • w = 0 := by
    rw [sub_smul, h, one_smul, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · apply hcube
    have h3 : c ^ 3 = c * c * c := by ring
    rw [h3]
    exact sub_eq_zero.mp h1
  · exact absurd h1 hw

theorem eig_corr {F : Type} [Field F] {g gi B Binv : Matrix (Fin 3) (Fin 3) F}
    (hg : g * gi = 1) (hgi : gi * g = 1) (hB : B * Binv = 1) (hBi : Binv * B = 1)
    (hgB : g * B = B * giᵀ) (φ v : Fin 3 → F) :
    (g *ᵥ (B *ᵥ φ) = B *ᵥ φ ↔ φ ᵥ* g = φ) ∧
      ((v ᵥ* Binv) ᵥ* g = v ᵥ* Binv ↔ g *ᵥ v = v) := by
  have hφ : φ ᵥ* gi = φ ↔ φ ᵥ* g = φ := by
    constructor
    · intro h
      calc φ ᵥ* g = (φ ᵥ* gi) ᵥ* g := by rw [h]
        _ = φ ᵥ* (gi * g) := by rw [Matrix.vecMul_vecMul]
        _ = φ := by rw [hgi, Matrix.vecMul_one]
    · intro h
      calc φ ᵥ* gi = (φ ᵥ* g) ᵥ* gi := by rw [h]
        _ = φ ᵥ* (g * gi) := by rw [Matrix.vecMul_vecMul]
        _ = φ := by rw [hg, Matrix.vecMul_one]
  have hB_inj : ∀ x y : Fin 3 → F, B *ᵥ x = B *ᵥ y ↔ x = y := by
    intro x y
    constructor
    · intro h
      calc x = (Binv * B) *ᵥ x := by rw [hBi, Matrix.one_mulVec]
        _ = Binv *ᵥ (B *ᵥ x) := by rw [Matrix.mulVec_mulVec]
        _ = Binv *ᵥ (B *ᵥ y) := by rw [h]
        _ = (Binv * B) *ᵥ y := by rw [Matrix.mulVec_mulVec]
        _ = y := by rw [hBi, Matrix.one_mulVec]
    · intro h
      rw [h]
  have hgB' : g *ᵥ (B *ᵥ φ) = B *ᵥ (giᵀ *ᵥ φ) := by
    calc g *ᵥ (B *ᵥ φ) = (g * B) *ᵥ φ := by rw [Matrix.mulVec_mulVec]
      _ = (B * giᵀ) *ᵥ φ := by rw [hgB]
      _ = B *ᵥ (giᵀ *ᵥ φ) := by rw [Matrix.mulVec_mulVec]
  have part1 : g *ᵥ (B *ᵥ φ) = B *ᵥ φ ↔ φ ᵥ* g = φ := by
    rw [hgB', hB_inj, Matrix.mulVec_transpose]
    exact hφ
  have hBg : Binv * g = giᵀ * Binv := by
    calc Binv * g = Binv * g * (B * Binv) := by rw [hB, mul_one]
      _ = Binv * (g * B) * Binv := by simp only [mul_assoc]
      _ = Binv * (B * giᵀ) * Binv := by rw [hgB]
      _ = giᵀ * Binv := by rw [← mul_assoc, hBi, one_mul]
  have hL : (v ᵥ* Binv) ᵥ* g = (gi *ᵥ v) ᵥ* Binv := by
    rw [Matrix.vecMul_vecMul, hBg, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose]
  have hR : ∀ x y : Fin 3 → F, x ᵥ* Binv = y ᵥ* Binv ↔ x = y := by
    intro x y
    constructor
    · intro h
      calc x = (x ᵥ* Binv) ᵥ* B := by rw [Matrix.vecMul_vecMul, hBi, Matrix.vecMul_one]
        _ = (y ᵥ* Binv) ᵥ* B := by rw [h]
        _ = y := by rw [Matrix.vecMul_vecMul, hBi, Matrix.vecMul_one]
    · intro h
      rw [h]
  have hV : gi *ᵥ v = v ↔ g *ᵥ v = v := by
    constructor
    · intro h
      calc g *ᵥ v = g *ᵥ (gi *ᵥ v) := by rw [h]
        _ = (g * gi) *ᵥ v := by rw [Matrix.mulVec_mulVec]
        _ = v := by rw [hg, Matrix.one_mulVec]
    · intro h
      calc gi *ᵥ v = gi *ᵥ (g *ᵥ v) := by rw [h]
        _ = (gi * g) *ᵥ v := by rw [Matrix.mulVec_mulVec]
        _ = v := by rw [hgi, Matrix.one_mulVec]
  have part2 : (v ᵥ* Binv) ᵥ* g = v ᵥ* Binv ↔ g *ᵥ v = v := by
    rw [hL]
    exact (hR _ _).trans hV
  exact ⟨part1, part2⟩

theorem mulVec_ne_zero_of {F : Type} [Field F] {B Binv : Matrix (Fin 3) (Fin 3) F}
    (hBi : Binv * B = 1) {v : Fin 3 → F} (hv : v ≠ 0) : B *ᵥ v ≠ 0 := by
  intro h0
  apply hv
  calc v = (Binv * B) *ᵥ v := by rw [hBi, Matrix.one_mulVec]
    _ = Binv *ᵥ (B *ᵥ v) := by rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [h0, Matrix.mulVec_zero]

theorem vecMul_ne_zero_of {F : Type} [Field F] {B Binv : Matrix (Fin 3) (Fin 3) F}
    (hB : B * Binv = 1) {φ : Fin 3 → F} (hφ : φ ≠ 0) : φ ᵥ* Binv ≠ 0 := by
  have hBi : Binv * B = 1 := mul_eq_one_comm.mp hB
  intro h0
  apply hφ
  calc φ = φ ᵥ* (Binv * B) := by rw [hBi, Matrix.vecMul_one]
    _ = (φ ᵥ* Binv) ᵥ* B := by rw [Matrix.vecMul_vecMul]
    _ = 0 := by rw [h0, Matrix.zero_vecMul]

theorem dot_vecMul_mulVec_cancel {F : Type} [Field F] {A Ai : Matrix (Fin 3) (Fin 3) F}
    (hA : Ai * A = 1) (φ v : Fin 3 → F) : (φ ᵥ* Ai) ⬝ᵥ (A *ᵥ v) = φ ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hA, Matrix.vecMul_one]

theorem eig_vec_one {F : Type} [Field F] {g : Matrix (Fin 3) (Fin 3) F} (hg3 : g * g * g = 1)
    (hcube : ∀ r : F, r ^ 3 = 1 → r = 1) {v : Fin 3 → F} (hv : v ≠ 0) (c : F)
    (h : g *ᵥ v = c • v) : g *ᵥ v = v := by
  have h1 : g *ᵥ (g *ᵥ (g *ᵥ v)) = (c * c * c) • v := by
    simp only [h, Matrix.mulVec_smul, smul_smul, mul_assoc]
  have h2 : (c * c * c) • v = v := by
    rw [← h1]
    calc g *ᵥ (g *ᵥ (g *ᵥ v)) = (g * g * g) *ᵥ v := by
          simp only [Matrix.mulVec_mulVec, mul_assoc]
      _ = v := by rw [hg3, Matrix.one_mulVec]
  have hc : c = 1 := eq_one_of_cube_smul hcube hv h2
  rw [h, hc, one_smul]

theorem eig_covec_one {F : Type} [Field F] {g gi : Matrix (Fin 3) (Fin 3) F}
    (hg : g * gi = 1) (hgi : gi * g = 1) (hg3 : g * g * g = 1)
    (hcube : ∀ r : F, r ^ 3 = 1 → r = 1) {φ : Fin 3 → F} (hφ : φ ≠ 0) (c : F)
    (h : φ ᵥ* gi = c • φ) : φ ᵥ* g = φ := by
  have hgi3 : gi * gi * gi = 1 := by
    calc gi * gi * gi = gi * gi * gi * (g * g * g) := by rw [hg3, mul_one]
      _ = gi * gi * (gi * g) * g * g := by simp only [mul_assoc]
      _ = gi * gi * g * g := by rw [hgi, mul_one]
      _ = gi * (gi * g) * g := by simp only [mul_assoc]
      _ = 1 := by rw [hgi, mul_one, hgi]
  have h1 : φ ᵥ* (gi * gi * gi) = (c * c * c) • φ := by
    calc φ ᵥ* (gi * gi * gi) = ((φ ᵥ* gi) ᵥ* gi) ᵥ* gi := by
          simp only [Matrix.vecMul_vecMul, mul_assoc]
      _ = (c * c * c) • φ := by
          simp only [h, Matrix.smul_vecMul, smul_smul, mul_assoc]
  have hgi1 : φ ᵥ* (gi * gi * gi) = φ := by rw [hgi3, Matrix.vecMul_one]
  have h2 : (c * c * c) • φ = φ := h1.symm.trans hgi1
  have hc : c = 1 := eq_one_of_cube_smul hcube hφ h2
  have hφgi : φ ᵥ* gi = φ := by rw [h, hc, one_smul]
  calc φ ᵥ* g = (φ ᵥ* gi) ᵥ* g := by rw [hφgi]
    _ = φ ᵥ* (gi * g) := by rw [Matrix.vecMul_vecMul]
    _ = φ := by rw [hgi, Matrix.vecMul_one]

end CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Vec

namespace CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Grp

theorem exists_involution_pow {G : Type} [Group G] {b : G} (hb : b ≠ 1) {k : ℕ}
    (hk : b ^ (2 ^ k) = 1) : ∃ j : ℕ, b ^ (2 ^ j) * b ^ (2 ^ j) = 1 ∧ b ^ (2 ^ j) ≠ 1 := by
  induction k with
  | zero =>
    exfalso
    apply hb
    simpa using hk
  | succ k ih =>
    by_cases h : b ^ (2 ^ k) = 1
    · exact ih h
    · refine ⟨k, ?_, h⟩
      have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      rw [h2, pow_add] at hk
      exact hk

theorem exists_central_involution {G : Type} [Group G] [Finite G] (D : Subgroup G) (hD0 : D ≠ ⊥)
    (hD2 : IsPGroup 2 D) : ∃ z ∈ D, z * z = 1 ∧ z ≠ 1 ∧ ∀ d ∈ D, z * d = d * z := by
  haveI : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).2 hD0
  haveI : Nontrivial (Subgroup.center D) := hD2.center_nontrivial
  obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center D)
  have hcD : (c : D) ≠ 1 := fun h => hc (Subtype.ext h)
  obtain ⟨k, hk⟩ := hD2 (c : D)
  obtain ⟨j, hj1, hj2⟩ := exists_involution_pow hcD hk
  have hcen : ∀ g : D, g * (c : D) = (c : D) * g := fun g => Subgroup.mem_center_iff.mp c.2 g
  obtain ⟨z, hz⟩ : ∃ z : D, z = (c : D) ^ 2 ^ j := ⟨_, rfl⟩
  rw [← hz] at hj1 hj2
  refine ⟨(z : G), z.2, ?_, ?_, ?_⟩
  · have h := congrArg Subtype.val hj1
    rw [Subgroup.coe_mul] at h
    exact h
  · intro h
    exact hj2 (Subtype.ext h)
  · intro d hd
    have hcomm : z * (⟨d, hd⟩ : D) = (⟨d, hd⟩ : D) * z := by
      have h1 : Commute (c : D) (⟨d, hd⟩ : D) := (hcen ⟨d, hd⟩).symm
      rw [hz]
      exact (h1.pow_left (2 ^ j)).eq
    have h2 : ((z * ⟨d, hd⟩ : D) : G) = ((⟨d, hd⟩ * z : D) : G) := congrArg Subtype.val hcomm
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
    exact h2

theorem map_surj_of_injective {G : Type} [Group G] [Finite G] (D : Subgroup G) (σ : G ≃* G)
    (hσD : ∀ d ∈ D, σ d ∈ D) : ∀ d ∈ D, ∃ d' ∈ D, σ d' = d := by
  have hf : Function.Injective (fun x : D => (⟨σ (x : G), hσD (x : G) x.2⟩ : D)) := by
    intro a b hab
    have h1 : σ (a : G) = σ (b : G) := congrArg Subtype.val hab
    exact Subtype.ext (σ.injective h1)
  intro d hd
  obtain ⟨d', hd'⟩ := Finite.surjective_of_injective hf ⟨d, hd⟩
  exact ⟨(d' : G), d'.2, congrArg Subtype.val hd'⟩

theorem exists_sl_conj {F : Type} [Field F] [Finite F] (hcube : ∀ r : F, r ^ 3 = 1 → r = 1)
    (B : GL (Fin 3) F) :
    ∃ b : SL(3, F), ∀ s : Matrix (Fin 3) (Fin 3) F,
      (B : Matrix (Fin 3) (Fin 3) F) * s * ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        (b : Matrix (Fin 3) (Fin 3) F) * s * ((b⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) := by
  have hinj : Function.Injective (fun x : F => x ^ 3) := by
    intro x y hxy
    have hxy' : x ^ 3 = y ^ 3 := hxy
    by_cases hy : y = 0
    · subst hy
      have hx : x ^ 3 = 0 := by rw [hxy', zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
      exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hx
    · have hr : (x * y⁻¹) ^ 3 = 1 := by
        rw [mul_pow, inv_pow, hxy', mul_inv_cancel₀ (pow_ne_zero 3 hy)]
      exact (mul_inv_eq_one₀ hy).mp (hcube _ hr)
  have hBB : (B : Matrix (Fin 3) (Fin 3) F) * ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
    Units.mul_inv B
  have hdet0 : Matrix.det (B : Matrix (Fin 3) (Fin 3) F) ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hBB
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  obtain ⟨t, ht⟩ := Finite.surjective_of_injective hinj (Matrix.det (B : Matrix (Fin 3) (Fin 3) F))
  have ht' : t ^ 3 = Matrix.det (B : Matrix (Fin 3) (Fin 3) F) := ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hdet0
    rw [← ht', zero_pow (by norm_num : (3 : ℕ) ≠ 0)]
  have hdet : Matrix.det (t⁻¹ • (B : Matrix (Fin 3) (Fin 3) F)) = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, ← ht', ← mul_pow, inv_mul_cancel₀ ht0, one_pow]
  obtain ⟨bSL, hbSL⟩ : ∃ b : SL(3, F),
      (b : Matrix (Fin 3) (Fin 3) F) = t⁻¹ • (B : Matrix (Fin 3) (Fin 3) F) :=
    ⟨⟨t⁻¹ • (B : Matrix (Fin 3) (Fin 3) F), hdet⟩, rfl⟩
  refine ⟨bSL, fun s => ?_⟩
  have hbM : (bSL : Matrix (Fin 3) (Fin 3) F) *
      (t • ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = 1 := by
    rw [hbSL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ht0, one_smul, hBB]
  have hcb : ((bSL⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) * (bSL : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hc : ((bSL⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      t • ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    have h1 : ((bSL⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
        ((bSL⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *
          ((bSL : Matrix (Fin 3) (Fin 3) F) *
            (t • ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) := by
      rw [hbM, mul_one]
    rw [h1, ← mul_assoc, hcb, one_mul]
  simp only [hc, hbSL, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ht0,
    mul_inv_cancel₀ ht0, one_smul]

end CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Grp
