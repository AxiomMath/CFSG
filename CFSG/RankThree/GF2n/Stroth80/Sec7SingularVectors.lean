module

public import Mathlib.FieldTheory.ChevalleyWarning
public import Mathlib.LinearAlgebra.QuadraticForm.Basis

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sec7_exists_singular_of_polar_zero {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (D : Submodule K V)
    (hD : Module.finrank K D = 2)
    (hiso : ∀ x ∈ D, ∀ y ∈ D, QuadraticMap.polar Q x y = 0) :
    ∃ p ∈ D, p ≠ 0 ∧ Q p = 0 := by
  have hF : ringChar K = 2 := ringChar.eq K 2
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  haveI : Module.Finite K D := Module.finite_of_finrank_pos (by omega)
  obtain ⟨e⟩ : Nonempty (Module.Basis (Fin 2) K D) := ⟨Module.finBasisOfFinrankEq K D hD⟩
  have hpair : ∀ s t : K, s • e 0 + t • e 1 = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have hg := Fintype.linearIndependent_iff.mp e.linearIndependent ![s, t] (by
      rw [Fin.sum_univ_two]
      simpa using h)
    exact ⟨by simpa using hg 0, by simpa using hg 1⟩
  obtain ⟨x, y, hxD, hyD, hxy⟩ : ∃ x y : V, x ∈ D ∧ y ∈ D ∧
      ∀ s t : K, s • x + t • y = 0 → s = 0 ∧ t = 0 :=
    ⟨↑(e 0), ↑(e 1), (e 0).2, (e 1).2, fun s t h => hpair s t (Subtype.ext (by simpa using h))⟩
  have hxy0 : QuadraticMap.polar Q x y = 0 := hiso x hxD y hyD
  have hadd : ∀ v w : V, Q (v + w) = Q v + Q w + QuadraticMap.polar Q v w :=
    QuadraticMap.map_add Q
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hF (Q x)
  obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two hF (Q y)
  by_cases hQx : Q x = 0
  · refine ⟨x, hxD, ?_, hQx⟩
    intro h0
    have h1 := (hxy 1 0 (by simp [h0])).1
    exact one_ne_zero h1
  · have hr0 : r ≠ 0 := by
      rintro rfl
      exact hQx (by rw [hr, mul_zero])
    refine ⟨t • x + r • y, D.add_mem (D.smul_mem t hxD) (D.smul_mem r hyD), ?_, ?_⟩
    · intro h0
      exact hr0 (hxy t r h0).2
    · rw [hadd, QuadraticMap.map_smul, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
        QuadraticMap.polar_smul_right, hxy0, hr, ht]
      simp only [smul_zero, add_zero, smul_eq_mul]
      linear_combination ((t * t) * (r * r)) * h2

theorem sec7_exists_ne_zero_zero_of_finrank_three {K M : Type*} [Field K] [Finite K]
    [AddCommGroup M] [Module K M] [FiniteDimensional K M] (Q' : QuadraticForm K M)
    (h3 : Module.finrank K M = 3) : ∃ z : M, z ≠ 0 ∧ Q' z = 0 := by
  classical
  have := Fintype.ofFinite K
  let b : Module.Basis (Fin 3) K M := Module.finBasisOfFinrankEq K M h3
  let B' := Q'.toBilin b
  let P : MvPolynomial (Fin 3) K := ∑ i, ∑ j,
    MvPolynomial.C (B' (b i) (b j)) * (MvPolynomial.X i * MvPolynomial.X j)
  have hdeg : P.totalDegree < Fintype.card (Fin 3) := by
    rw [Fintype.card_fin]
    have h2 : P.totalDegree ≤ 2 := by
      refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
      refine MvPolynomial.totalDegree_finsetSum_le fun j _ => ?_
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    omega
  have heval : ∀ x : Fin 3 → K, MvPolynomial.eval x P = Q' (∑ i, x i • b i) := by
    intro x
    have hQ : Q' (∑ i, x i • b i) = B' (∑ i, x i • b i) (∑ i, x i • b i) := by
      conv_lhs => rw [← QuadraticMap.toQuadraticMap_toBilin Q' b]
      rfl
    rw [hQ, LinearMap.map_sum₂]
    simp only [P, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, smul_eq_mul]
    ring
  have hpr : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have hdvd := char_dvd_card_solutions (K := K) (σ := Fin 3) (ringChar K) hdeg
  have h0 : MvPolynomial.eval (0 : Fin 3 → K) P = 0 := by
    rw [heval]
    simp
  have hpos : 0 < Fintype.card { x : Fin 3 → K // MvPolynomial.eval x P = 0 } :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have hone : 1 < Fintype.card { x : Fin 3 → K // MvPolynomial.eval x P = 0 } := by
    have := Nat.le_of_dvd hpos hdvd
    have hp2 := hpr.two_le
    omega
  obtain ⟨⟨x, hx⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hone ⟨0, h0⟩
  have hx0 : x ≠ 0 := fun h => hne (Subtype.ext h)
  refine ⟨∑ i, x i • b i, fun h => hx0 ?_, by rw [← heval]; exact hx⟩
  exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent x h)

theorem sec7_exists_singular_of_finrank_three {K V : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (D : Submodule K V)
    (hD : Module.finrank K D = 3) : ∃ p ∈ D, p ≠ 0 ∧ Q p = 0 := by
  haveI : Module.Finite K D := Module.finite_of_finrank_pos (by omega)
  obtain ⟨z, hz0, hz⟩ := sec7_exists_ne_zero_zero_of_finrank_three (Q.comp D.subtype) hD
  exact ⟨z.1, z.2, fun h => hz0 (Subtype.ext h), hz⟩

end CFSG.RankThree.GF2n.Stroth80
