module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import CFSG.RankThree.PartOne.KEXC.BTSL2

public section

namespace CFSG.RankThree.PartOne.S15K

open Matrix CFSG.RankThree.PartOne.KEXC
open scoped commutatorElement

section Transvection

variable {F : Type*} [Field F]

@[expose] def omega2 (a b : Fin 2 → F) : F := a 0 * b 1 - a 1 * b 0

@[expose] def tvM (v : Fin 2 → F) (x : F) : Matrix (Fin 2) (Fin 2) F :=
  !![1 - x * v 0 * v 1, x * v 0 ^ 2; -(x * v 1 ^ 2), 1 + x * v 0 * v 1]

theorem tvM_mulVec (v : Fin 2 → F) (x : F) (u : Fin 2 → F) :
    tvM v x *ᵥ u = u + (x * omega2 v u) • v := by
  funext i
  fin_cases i <;> simp [tvM, omega2, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem det_tvM (v : Fin 2 → F) (x : F) : (tvM v x).det = 1 := by
  simp only [tvM, Matrix.det_fin_two_of]
  ring

@[expose] def tvSL (v : Fin 2 → F) (x : F) : SpecialLinearGroup (Fin 2) F := ⟨tvM v x, det_tvM v x⟩

theorem tvSL_zero (v : Fin 2 → F) : tvSL v 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tvSL, tvM]

theorem tvM_mul (v : Fin 2 → F) (x y : F) : tvM v x * tvM v y = tvM v (x + y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tvM, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem tvSL_mul (v : Fin 2 → F) (x y : F) : tvSL v x * tvSL v y = tvSL v (x + y) :=
  Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul]; exact tvM_mul v x y)

theorem tvSL_mul_comm (v : Fin 2 → F) (x y : F) : tvSL v x * tvSL v y = tvSL v y * tvSL v x := by
  rw [tvSL_mul, tvSL_mul, add_comm]

@[expose] def tvHom (v : Fin 2 → F) : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun x := tvSL v (Multiplicative.toAdd x)
  map_one' := tvSL_zero v
  map_mul' := fun _ _ => (tvSL_mul v _ _).symm

theorem tvHom_apply (v : Fin 2 → F) (x : F) : tvHom v (Multiplicative.ofAdd x) = tvSL v x := rfl

theorem tvSL_inv_of_charTwo [CharP F 2] (v : Fin 2 → F) (x : F) : (tvSL v x)⁻¹ = tvSL v x := by
  rw [inv_eq_iff_mul_eq_one, tvSL_mul]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have : x + x = 0 := by rw [← two_mul, h2, zero_mul]
  rw [this, tvSL_zero]

theorem tvSL_ne_one {v : Fin 2 → F} (hv : v ≠ 0) : tvSL v 1 ≠ 1 := by
  intro h
  have h' := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  have h'' := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have h''' := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 1) h
  simp [tvSL, tvM] at h' h'' h'''
  apply hv
  funext i
  fin_cases i
  · simpa using h'
  · have : v 1 ^ 2 = 0 := by
      have := congrArg (fun g : SpecialLinearGroup (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F) 1 0) h
      simpa [tvSL, tvM] using this
    simpa using this

theorem omega2_smul_left (c : F) (a b : Fin 2 → F) : omega2 (c • a) b = c * omega2 a b := by
  simp only [omega2, Pi.smul_apply, smul_eq_mul]
  ring

theorem omega2_smul (g : SpecialLinearGroup (Fin 2) F) (a b : Fin 2 → F) :
    omega2 (g • a) (g • b) = omega2 a b := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  simp only [omega2, slTwoAct_def, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (a 0 * b 1 - a 1 * b 0) * hdet

theorem tvSL_conj {g : SpecialLinearGroup (Fin 2) F} {v : Fin 2 → F} {ζ : F} (hζ : ζ ≠ 0)
    (hg : g • v = ζ • v) (x : F) : g * tvSL v x * g⁻¹ = tvSL v (ζ ^ 2 * x) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  have h1 : (tvSL v x : Matrix (Fin 2) (Fin 2) F) *ᵥ u = u + (x * omega2 v u) • v :=
    tvM_mulVec v x u
  have h2 : (tvSL v (ζ ^ 2 * x) : Matrix (Fin 2) (Fin 2) F) *ᵥ ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ u) =
      (g : Matrix (Fin 2) (Fin 2) F) *ᵥ u +
        ((ζ ^ 2 * x) * omega2 v ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ u)) • v :=
    tvM_mulVec v (ζ ^ 2 * x) _
  have hgv : (g : Matrix (Fin 2) (Fin 2) F) *ᵥ v = ζ • v := hg
  have hom : ζ * omega2 v ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ u) = omega2 v u := by
    have := omega2_smul g v u
    rw [hg, omega2_smul_left] at this
    exact this
  rw [h1, h2, Matrix.mulVec_add, Matrix.mulVec_smul, hgv]
  congr 1
  rw [smul_smul]
  congr 1
  have hom' : omega2 v ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ u) = ζ⁻¹ * omega2 v u := by
    rw [← hom, ← mul_assoc, inv_mul_cancel₀ hζ, one_mul]
  rw [hom']
  field_simp

end Transvection

section Eigenvector

variable {F : Type*} [Field F] [Finite F]

theorem exists_eigenvector_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card F - 1)
    {g : SpecialLinearGroup (Fin 2) F} (hg : g ^ p = 1) :
    ∃ (v : Fin 2 → F) (ζ : F), v ≠ 0 ∧ ζ ^ p = 1 ∧ g • v = ζ • v := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨ζ₀, hζ₀⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hprim : IsPrimitiveRoot (ζ₀ : F) p := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hζ₀]
    exact IsPrimitiveRoot.orderOf ζ₀
  have hsplit : (Polynomial.X ^ p - 1 : Polynomial F).Splits := by
    rw [Polynomial.X_pow_sub_one_eq_prod hp.pos hprim]
    exact Polynomial.Splits.prod fun ζ _ => Polynomial.Splits.X_sub_C ζ
  set f : Module.End F (Fin 2 → F) := Matrix.toLinAlgEquiv' (g : Matrix (Fin 2) (Fin 2) F) with hf
  have hfp : f ^ p = 1 := by
    have : (g : Matrix (Fin 2) (Fin 2) F) ^ p = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hg, Matrix.SpecialLinearGroup.coe_one]
    rw [hf, ← map_pow, this, map_one]
  have hroot : Polynomial.aeval f (Polynomial.X ^ p - 1 : Polynomial F) = 0 := by
    simp [hfp]
  have hdvd' : minpoly F f ∣ (Polynomial.X ^ p - 1 : Polynomial F) := minpoly.dvd F f hroot
  have hne : (Polynomial.X ^ p - 1 : Polynomial F) ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero hp.pos (1 : F)
  have hsplit' : (minpoly F f).Splits := hsplit.of_dvd hne hdvd'
  have hint : IsIntegral F f := IsIntegral.of_finite F f
  obtain ⟨μ, hμ⟩ := hsplit'.exists_eval_eq_zero (minpoly.degree_pos hint).ne'
  have hμp : μ ^ p = 1 := by
    obtain ⟨q, hq⟩ := hdvd'
    have := congrArg (Polynomial.eval μ) hq
    simp [hμ] at this
    exact sub_eq_zero.1 this
  have hev : f.HasEigenvalue μ := Module.End.hasEigenvalue_of_isRoot hμ
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  exact ⟨v, μ, hv.2, hμp, by simpa [hf, slTwoAct_def, Matrix.toLinAlgEquiv'_apply] using hv.apply_eq_smul⟩

end Eigenvector

section TwoSubgroup

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem exists_two_subgroup_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F - 1) {g : SpecialLinearGroup (Fin 2) F} (hg1 : g ≠ 1) (hgp : g ^ p = 1) :
    ∃ S : Subgroup (SpecialLinearGroup (Fin 2) F), S ≠ ⊥ ∧ IsPGroup 2 S ∧
      g ∈ Subgroup.normalizer (S : Set (SpecialLinearGroup (Fin 2) F)) ∧
      ⁅S, Subgroup.zpowers g⁆ = S := by
  obtain ⟨v, ζ, hv, hζp, hgv⟩ := exists_eigenvector_of_pow_eq_one hp hpq hgp
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζp
    exact zero_ne_one hζp
  have hζ1 : ζ ≠ 1 := by
    rintro rfl
    rw [one_smul] at hgv
    have hsq := slTwo_sq_eq_one hv hgv
    apply hg1
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    have : g ^ p = g := by rw [hk, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul]
    rw [← this]
    exact hgp
  have hne : (1 : F) + ζ ^ 2 ≠ 0 := by
    have h1 : (1 : F) + ζ ^ 2 = (1 + ζ) ^ 2 := by linear_combination (-ζ) * h2
    rw [h1]
    refine pow_ne_zero 2 fun h => hζ1 ?_
    have : ζ = -1 := by linear_combination h
    rw [this, CharTwo.neg_eq]
  have hconj : ∀ x : F, g * tvSL v x * g⁻¹ = tvSL v (ζ ^ 2 * x) := fun x => tvSL_conj hζ0 hgv x
  have hnorm : g ∈ Subgroup.normalizer (((tvHom v).range : Subgroup (SpecialLinearGroup (Fin 2) F)) :
      Set (SpecialLinearGroup (Fin 2) F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨Multiplicative.ofAdd (ζ ^ 2 * Multiplicative.toAdd y), ?_⟩
      have e1 : tvHom v (Multiplicative.ofAdd (ζ ^ 2 * Multiplicative.toAdd y)) =
          tvSL v (ζ ^ 2 * Multiplicative.toAdd y) := tvHom_apply v _
      have e2 : tvHom v y = tvSL v (Multiplicative.toAdd y) := by
        have := tvHom_apply v (Multiplicative.toAdd y)
        rwa [ofAdd_toAdd] at this
      rw [e1, e2]
      exact (hconj _).symm
    · rintro ⟨y, hy⟩
      refine ⟨Multiplicative.ofAdd ((ζ ^ 2)⁻¹ * Multiplicative.toAdd y), ?_⟩
      have h1 : tvSL v (ζ ^ 2 * ((ζ ^ 2)⁻¹ * Multiplicative.toAdd y)) = tvSL v (Multiplicative.toAdd y) := by
        rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hζ0), one_mul]
      have h2 : g * tvSL v ((ζ ^ 2)⁻¹ * Multiplicative.toAdd y) * g⁻¹ = g * h * g⁻¹ := by
        rw [hconj, h1]
        exact hy
      have h3 : tvSL v ((ζ ^ 2)⁻¹ * Multiplicative.toAdd y) = h :=
        mul_left_cancel (mul_right_cancel h2)
      exact h3
  refine ⟨(tvHom v).range, ?_, ?_, hnorm, ?_⟩
  · intro h
    have hmem : tvSL v 1 ∈ (tvHom v).range := ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact tvSL_ne_one hv hmem
  · intro x
    refine ⟨1, ?_⟩
    obtain ⟨y, hy⟩ := x.2
    apply Subtype.ext
    rw [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one, ← hy]
    show tvSL v (Multiplicative.toAdd y) * tvSL v (Multiplicative.toAdd y) = 1
    rw [tvSL_mul, ← two_mul, h2, zero_mul, tvSL_zero]
  · apply le_antisymm
    · exact Subgroup.le_normalizer_iff_commutator_le_left.1 (by rw [Subgroup.zpowers_le]; exact hnorm)
    · rintro _ ⟨y, rfl⟩
      set a := Multiplicative.toAdd y with ha
      have hcomm : ⁅tvSL v ((1 + ζ ^ 2)⁻¹ * a), g⁆ =
          tvSL v ((1 + ζ ^ 2)⁻¹ * a) * (g * tvSL v ((1 + ζ ^ 2)⁻¹ * a) * g⁻¹) := by
        rw [commutatorElement_def, tvSL_inv_of_charTwo]
        group
      have hx : tvHom v y = ⁅tvSL v ((1 + ζ ^ 2)⁻¹ * a), g⁆ := by
        rw [hcomm, hconj, tvSL_mul]
        have e2 : tvHom v y = tvSL v a := by
          have := tvHom_apply v a
          rwa [ha, ofAdd_toAdd] at this
        rw [e2]
        congr 1
        field_simp
      rw [hx]
      exact Subgroup.commutator_mem_commutator
        (show tvSL v ((1 + ζ ^ 2)⁻¹ * a) ∈ (tvHom v).range from ⟨Multiplicative.ofAdd _, rfl⟩)
        (Subgroup.mem_zpowers g)

end TwoSubgroup

end CFSG.RankThree.PartOne.S15K
