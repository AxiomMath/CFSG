module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import CFSG.Mathlib.FieldTheory.Finite.QuadraticZero
import CFSG.ClassicalInvolution.Phan.PhanS22Witt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open QuadraticMap Matrix

private noncomputable def quadPoly {k : Type*} [Field k] {d : ℕ}
    (B : LinearMap.BilinForm k (Fin d → k)) : MvPolynomial (Fin d) k :=
  ∑ i, ∑ j, MvPolynomial.C (B (Pi.single i 1) (Pi.single j 1)) * MvPolynomial.X i *
    MvPolynomial.X j

private lemma quadPoly_totalDegree {k : Type*} [Field k] {d : ℕ}
    (B : LinearMap.BilinForm k (Fin d → k)) : (quadPoly B).totalDegree ≤ 2 := by
  rw [quadPoly]
  refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
  refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
  have h1 := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (B (Pi.single i 1) (Pi.single j 1)) * MvPolynomial.X i :
      MvPolynomial (Fin d) k) (MvPolynomial.X j)
  have h2 := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (B (Pi.single i 1) (Pi.single j 1)) : MvPolynomial (Fin d) k)
    (MvPolynomial.X i)
  simp only [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C] at h1 h2
  omega

private lemma eval_quadPoly {k : Type*} [Field k] {d : ℕ}
    (B : LinearMap.BilinForm k (Fin d → k)) (v : Fin d → k) :
    MvPolynomial.eval v (quadPoly B) =
      ∑ i, ∑ j, v i * (v j * B (Pi.single i 1) (Pi.single j 1)) := by
  rw [quadPoly]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma eval_quadPoly_polar {k : Type*} [Field k] {d : ℕ}
    (Q : QuadraticForm k (Fin d → k)) (v : Fin d → k) :
    MvPolynomial.eval v (quadPoly (polarBilin Q)) = polar Q v v := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin d → k) := by
    conv_lhs => rw [pi_eq_sum_univ v]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : (fun j => if i = j then (1 : k) else 0) = (Pi.single i 1 : Fin d → k) := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [h]
  rw [eval_quadPoly]
  have hpol : polar Q v v =
      ∑ i, ∑ j, v i * (v j * polar Q (Pi.single i 1) (Pi.single j 1)) := by
    conv_lhs => rw [hv]
    rw [CFSG.ClassicalInvolution.PhanB3.S.Std.Q7.Witt.polar_sum_smul]
  rw [hpol]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [QuadraticMap.polarBilin_apply_apply]

private lemma eq_zero_of_two_nsmul_eq_zero {k : Type*} [Field k] (hk : ringChar k ≠ 2)
    {a : k} (h : (2 : ℕ) • a = 0) : a = 0 := by
  rw [two_nsmul] at h
  have h2 : (2 : k) * a = 0 := by
    rw [two_mul]
    exact h
  exact (mul_eq_zero.mp h2).resolve_left (Ring.two_ne_zero hk)

theorem exists_singular_of_three_le_finrank {k V : Type*} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) [AddCommGroup V] [Module k V] (Q : QuadraticForm k V)
    {W : Submodule k V} (hW : 3 ≤ Module.finrank k W) : ∃ w ∈ W, w ≠ 0 ∧ Q w = 0 := by
  classical
  let := Fintype.ofFinite k
  have hfin : Module.Finite k W := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin (Module.finrank k W)) k W := Module.finBasis k W
  obtain ⟨x, hx0, hx⟩ :=
    CFSG.FiniteField.exists_ne_zero_dotProduct_mulVec_eq_zero (K := k)
      (σ := Fin (Module.finrank k W)) (by simpa using hW)
      (Matrix.of fun i j => polar Q (b i : V) (b j : V))
  let v : V := ∑ i, x i • (b i : V)
  have hvW : v ∈ W := W.sum_mem fun i _ => W.smul_mem _ (b i).2
  have hvne : v ≠ 0 := by
    intro h0
    have h1 : ∑ i, x i • (b i : W) = 0 := by
      apply Subtype.ext
      simpa [v] using h0
    exact hx0 (funext fun i => (Fintype.linearIndependent_iff.mp b.linearIndependent) x h1 i)
  have hvQ : Q v = 0 := by
    have hM : x ⬝ᵥ (Matrix.of (fun i j => polar Q (b i : V) (b j : V)) *ᵥ x) =
        ∑ i, ∑ j, x i * (x j * polar Q (b i : V) (b j : V)) := by
      rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.of_apply]
      ring
    have hsum0 : ∑ i, ∑ j, x i * (x j * polar Q (b i : V) (b j : V)) = 0 := by
      rw [← hM]
      exact hx
    have hpolar : polar Q v v = 0 := by
      conv_lhs => rw [show v = ∑ i, x i • (b i : V) from rfl]
      rw [CFSG.ClassicalInvolution.PhanB3.S.Std.Q7.Witt.polar_sum_smul]
      exact hsum0
    have h2 : (2 : ℕ) • Q v = 0 := by
      rw [← polar_self, hpolar]
    exact eq_zero_of_two_nsmul_eq_zero hk h2
  exact ⟨v, hvW, hvne, hvQ⟩

theorem exists_common_singular {k : Type*} [Field k] [Finite k] (hk : ringChar k ≠ 2) {d : ℕ}
    (hd : 5 ≤ d) (Q₁ Q₂ : QuadraticForm k (Fin d → k)) :
    ∃ v : Fin d → k, v ≠ 0 ∧ Q₁ v = 0 ∧ Q₂ v = 0 := by
  classical
  let := Fintype.ofFinite k
  have hprime : (ringChar k).Prime := CharP.char_is_prime k (ringChar k)
  have : Fact (ringChar k).Prime := ⟨hprime⟩
  let p₁ : MvPolynomial (Fin d) k := quadPoly (polarBilin Q₁)
  let p₂ : MvPolynomial (Fin d) k := quadPoly (polarBilin Q₂)
  have hlt : p₁.totalDegree + p₂.totalDegree < Fintype.card (Fin d) := by
    have h1 := quadPoly_totalDegree (polarBilin Q₁)
    have h2 := quadPoly_totalDegree (polarBilin Q₂)
    simp only [p₁, p₂, Fintype.card_fin]
    omega
  have hdvd := char_dvd_card_solutions_of_add_lt (p := ringChar k) (f₁ := p₁) (f₂ := p₂) hlt
  have h0 : MvPolynomial.eval (0 : Fin d → k) p₁ = 0 ∧
      MvPolynomial.eval (0 : Fin d → k) p₂ = 0 := by
    simp only [p₁, p₂, eval_quadPoly_polar]
    simp
  have hpos : 0 < Fintype.card {x : Fin d → k //
      MvPolynomial.eval x p₁ = 0 ∧ MvPolynomial.eval x p₂ = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have h1lt : 1 < Fintype.card {x : Fin d → k //
      MvPolynomial.eval x p₁ = 0 ∧ MvPolynomial.eval x p₂ = 0} := by
    have hp := Nat.le_of_dvd hpos hdvd
    exact lt_of_lt_of_le (by norm_num) (le_trans hprime.two_le hp)
  obtain ⟨x, hx0⟩ := Fintype.exists_ne_of_one_lt_card h1lt ⟨0, h0⟩
  have hx1 : polar Q₁ x.1 x.1 = 0 := by
    have h : MvPolynomial.eval x.1 (quadPoly (polarBilin Q₁)) = 0 := x.2.1
    rwa [eval_quadPoly_polar] at h
  have hx2 : polar Q₂ x.1 x.1 = 0 := by
    have h : MvPolynomial.eval x.1 (quadPoly (polarBilin Q₂)) = 0 := x.2.2
    rwa [eval_quadPoly_polar] at h
  have hq1 : Q₁ x.1 = 0 := by
    have h2 : (2 : ℕ) • Q₁ x.1 = 0 := by
      rw [← polar_self, hx1]
    exact eq_zero_of_two_nsmul_eq_zero hk h2
  have hq2 : Q₂ x.1 = 0 := by
    have h2 : (2 : ℕ) • Q₂ x.1 = 0 := by
      rw [← polar_self, hx2]
    exact eq_zero_of_two_nsmul_eq_zero hk h2
  refine ⟨x.1, ?_, hq1, hq2⟩
  intro hv
  exact hx0 (Subtype.ext hv)

theorem exists_polar_eq_one_of_notMem_span {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {Q : QuadraticForm k V} (hQ : (polarBilin Q).Nondegenerate)
    {u₁ u₂ z : V} (hz : z ∉ Submodule.span k {u₁, u₂}) :
    ∃ y : V, polar Q u₁ y = 0 ∧ polar Q u₂ y = 0 ∧ polar Q z y = 1 := by
  classical
  obtain ⟨f, hfz, hle⟩ := Submodule.exists_le_ker_of_notMem hz
  let g : V →ₗ[k] k := (f z)⁻¹ • f
  have hgz : g z = 1 := by
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hfz]
  have hgu₁ : g u₁ = 0 := by
    have h : f u₁ = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span (by simp)))
    rw [LinearMap.smul_apply, smul_eq_mul, h, mul_zero]
  have hgu₂ : g u₂ = 0 := by
    have h : f u₂ = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span (by simp)))
    rw [LinearMap.smul_apply, smul_eq_mul, h, mul_zero]
  let y : V := (LinearMap.BilinForm.toDual (polarBilin Q) hQ).symm g
  have happly : ∀ v : V, polar Q y v = g v := by
    intro v
    rw [← QuadraticMap.polarBilin_apply_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [polar_comm Q u₁ y, happly, hgu₁]
  · rw [polar_comm Q u₂ y, happly, hgu₂]
  · rw [polar_comm Q z y, happly, hgz]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
