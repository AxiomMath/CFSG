module

public import CFSG.Walter.Ree.Bombieri.Eliminant
public import CFSG.Walter.Ree.Bombieri.Kernel
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import CFSG.Walter.Ree.Bombieri.Appendix

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Elim

open MvPolynomial

abbrev D : ℕ := 114

noncomputable def P : Polynomial A5 := finSuccEquiv (ZMod 3) 5 Pmv

noncomputable def P' : Polynomial A5 := finSuccEquiv (ZMod 3) 5 Pmv'

noncomputable def ζA : A5 := 1 + X 1 * X 0 ^ 2

noncomputable def P1 : Polynomial A5 :=
  ∑ j ∈ Finset.range (D + 1), Polynomial.C (P'.coeff j * ζA ^ j) * Polynomial.X ^ (2 * D - 2 * j)

noncomputable def H0 : A5 := Polynomial.resultant P P1 D (2 * D)

theorem H0_eq : H0 = Polynomial.resultant P P1 D (2 * D) := by rw [H0]

theorem natDegree_P : P.natDegree ≤ D := by
  rw [P, natDegree_finSuccEquiv]; exact degreeOf_Pmv.1

theorem natDegree_P' : P'.natDegree ≤ D := by
  rw [P', natDegree_finSuccEquiv]; exact degreeOf_Pmv'.1

theorem natDegree_P1 : P1.natDegree ≤ 2 * D := by
  unfold P1
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

@[expose] def dP : Fin 5 → ℕ := ![122, 78, 42, 12, 0]

@[expose] def dP' : Fin 5 → ℕ := ![0, 122, 78, 42, 12]

@[expose] def dP1 : Fin 5 → ℕ := ![2 * D, 122 + D, 78, 42, 12]

theorem degreeOf_coeff_P (i : Fin 5) (j : ℕ) : (P.coeff j).degreeOf i ≤ dP i := by
  refine (degreeOf_coeff_finSuccEquiv _ i j).trans ?_
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := degreeOf_Pmv
  fin_cases i
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · simp [dP, h5]

theorem degreeOf_coeff_P' (i : Fin 5) (j : ℕ) : (P'.coeff j).degreeOf i ≤ dP' i := by
  refine (degreeOf_coeff_finSuccEquiv _ i j).trans ?_
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := degreeOf_Pmv'
  fin_cases i
  · simp [dP', h1]
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem degreeOf_ζA (i : Fin 5) : ζA.degreeOf i ≤ ![2, 1, 0, 0, 0] i := by
  unfold ζA
  refine (degreeOf_add_le _ _ _).trans (max_le (by simp) ?_)
  refine (degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add (le_refl _) (degreeOf_pow_le _ _ _)).trans ?_
  fin_cases i <;> simp [degreeOf_X]

theorem coeff_P1 (n : ℕ) :
    P1.coeff n = ∑ j ∈ Finset.range (D + 1),
      if n = 2 * D - 2 * j then P'.coeff j * ζA ^ j else 0 := by
  simp only [P1, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]

theorem degreeOf_coeff_P1 (i : Fin 5) (n : ℕ) : (P1.coeff n).degreeOf i ≤ dP1 i := by
  rw [coeff_P1]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun j hj => ?_)
  have hjD : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  split_ifs
  · refine (degreeOf_mul_le _ _ _).trans ?_
    refine (add_le_add (degreeOf_coeff_P' i j) (degreeOf_pow_le _ _ _)).trans ?_
    have hz := Nat.mul_le_mul_left j (degreeOf_ζA i)
    refine (Nat.add_le_add_left hz _).trans ?_
    fin_cases i <;> simp [dP', dP1] <;> omega
  · simp

@[expose] def dH0 : Fin 5 → ℕ := ![53808, 44688, 18468, 7524, 1368]

theorem H0_degreeOf (i : Fin 5) : H0.degreeOf i ≤ dH0 i := by
  unfold H0 Polynomial.resultant
  let κ : Fin (D + 2 * D) → ℕ := fun j => Fin.addCases (fun _ => dP1 i) (fun _ => dP i) j
  refine (degreeOf_det_le i _ (fun _ => 0) κ fun r c => ?_).trans ?_
  · simp only [zero_add, Polynomial.sylvester, Matrix.of_apply, κ]
    induction c using Fin.addCases with
    | left c => simp only [Fin.addCases_left]; split_ifs <;> simp [degreeOf_coeff_P1]
    | right c => simp only [Fin.addCases_right]; split_ifs <;> simp [degreeOf_coeff_P]
  · simp only [Finset.sum_const_zero, zero_add, Fin.sum_univ_add, κ, Fin.addCases_left,
      Fin.addCases_right, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    fin_cases i <;> simp [dP, dP1, dH0] <;> decide

theorem map_matOf {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S) (ρ : ℕ → R) :
    h.mapMatrix (matOf ρ) = matOf (h ∘ ρ) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, matOf, Matrix.of_apply]
  rw [PE.map_eval]
  congr 1
  funext k
  simp only [Function.comp_apply, atomsOf, PE.map_eval]
  congr 1
  funext _
  simp

variable {K : Type*} [Field K] [CharP K 3]

noncomputable def evM6 (t : K) (zs : Fin 5 → K) : M6 →+* K :=
  eval₂Hom (castThree K) (Fin.cons t zs)

noncomputable def evA5 (zs : Fin 5 → K) : A5 →+* K := eval₂Hom (castThree K) zs

theorem evA5_ζA (zs : Fin 5 → K) : evA5 zs ζA = 1 + zs 1 * zs 0 ^ 2 := by
  simp [evA5, ζA]

theorem evA5_X (zs : Fin 5 → K) (i : Fin 5) : evA5 zs (X i) = zs i := by simp [evA5]

theorem evA5_C (zs : Fin 5 → K) (c : ZMod 3) : evA5 zs (C c) = castThree K c := by
  simp [evA5]

theorem eval_finSuccEquiv (t : K) (zs : Fin 5 → K) (f : M6) :
    Polynomial.eval₂ (evA5 zs) t (finSuccEquiv (ZMod 3) 5 f) = evM6 t zs f := by
  have : (Polynomial.eval₂RingHom (evA5 zs) t).comp (finSuccEquiv (ZMod 3) 5).toRingHom =
      evM6 t zs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [evM6, evA5, finSuccEquiv_apply]
    · intro i
      induction i using Fin.cases with
      | zero => simp [evM6, finSuccEquiv_X_zero]
      | succ j => simp [evM6, evA5, finSuccEquiv_X_succ]
  exact congrArg (fun g : M6 →+* K => g f) this

theorem eval_P (t : K) (zs : Fin 5 → K) :
    Polynomial.eval₂ (evA5 zs) t P = (matOf (ptVars (zs 0) (zs 1) (zs 2) (zs 3) t)).det := by
  rw [P, eval_finSuccEquiv, Pmv_eq, RingHom.map_det, map_matOf]
  congr 2
  funext i
  rcases i with _ | _ | _ | _ | _ | i <;> simp [varsP, ptVars, evM6] <;> rfl

theorem eval_P' (t : K) (zs : Fin 5 → K) :
    Polynomial.eval₂ (evA5 zs) t P' = (matOf (ptVars (zs 1) (zs 2) (zs 3) (zs 4) t)).det := by
  rw [P', eval_finSuccEquiv, Pmv'_eq, RingHom.map_det,
    map_matOf]
  congr 2
  funext i
  rcases i with _ | _ | _ | _ | _ | i <;> simp [varsP', ptVars, evM6] <;> rfl

theorem eval_P1 (y : K) (zs : Fin 5 → K) {y1 : K} (hy : evA5 zs ζA = y1 * y ^ 2) :
    Polynomial.eval₂ (evA5 zs) y P1 = y ^ (2 * D) * Polynomial.eval₂ (evA5 zs) y1 P' := by
  rw [Polynomial.eval₂_eq_sum_range' (evA5 zs) (Nat.lt_succ_of_le natDegree_P') y1, P1,
    Polynomial.eval₂_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjD : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, map_mul, map_pow, hy,
    mul_pow, ← pow_mul]
  have : y ^ (2 * D) = y ^ (2 * j) * y ^ (2 * D - 2 * j) := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  ring

theorem H0_eval_eq_zero {σ : K ≃+* K} {a : ℕ} (hB : ∀ x : K, (σ x * x) ^ a = x ^ 2)
    (hC : ∀ p ∈ ESigma K σ, thompsonT a p.1 p.2.1 p.2.2 = 0) {p : K × K × K}
    (hp : p ∈ ESigma K σ) : evA5 (fun i => (σ ^ (i : ℕ)) p.1) H0 = 0 := by
  obtain ⟨z, y, u⟩ := p
  set zs : Fin 5 → K := fun i => (σ ^ (i : ℕ)) z with hzs
  have hz0 : zs 0 = z := by simp [zs]
  have hz1 : zs 1 = σ z := by simp [zs]
  have hz2 : zs 2 = σ (σ z) := by simp [zs]
  have hz3 : zs 3 = σ (σ (σ z)) := by simp [zs]
  have hz4 : zs 4 = σ (σ (σ (σ z))) := by simp [zs]
  obtain ⟨pp, qq, -, -, hpq⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant P P1
    natDegree_P natDegree_P1 (Or.inl (by norm_num))
  have h := congrArg (Polynomial.eval₂ (evA5 zs) y) hpq
  rw [Polynomial.eval₂_C, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul] at h
  change _ = evA5 zs H0 at h
  rw [← h]
  have hP : Polynomial.eval₂ (evA5 zs) y P = 0 := by
    rw [eval_P, hz0, hz1, hz2, hz3]
    have h0 := det_matOf_eq_zero hB hC hp
    simp only at h0
    exact h0
  have hζ : evA5 zs ζA = σ y * y ^ 2 := by
    have := hp.1
    simp only [ζA, map_add, map_one, map_mul, map_pow, evA5, eval₂Hom_X'] at this ⊢
    rw [hz0, hz1]
    linear_combination this
  have hP1 : Polynomial.eval₂ (evA5 zs) y P1 = 0 := by
    rw [eval_P1 y zs hζ, eval_P', hz1, hz2, hz3, hz4]
    have h0 := det_matOf_eq_zero hB hC (ESigma.map hp)
    rw [h0, mul_zero]
  rw [hP, hP1]; ring

end Elim

end CFSG.Walter.Ree.Bombieri
