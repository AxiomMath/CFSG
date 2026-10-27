module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergTrialityModel

public section

namespace CFSG.StandardType

namespace Triality

open CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.SpinFrame CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms QuadraticMap

variable {K : Type} [Field K]

@[expose] def ImTwo {d : ℕ} (A : Matrix (Fin d) (Fin d) K) : Prop :=
  ∃ a b : Fin d → K, ∀ y, Matrix.mulVec A y - y ∈ Submodule.span K {a, b}

theorem imTwo_conjAct {d : ℕ} {Q : QuadraticForm K (Fin d → K)} (g : similarityPairs Q)
    {X : matrixDerived Q} (hX : ImTwo ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) :
    ImTwo (((conjAct Q g X : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  obtain ⟨a, b, hab⟩ := hX
  set S := coordinateSemilinearMap g.val
  refine ⟨S a, S b, fun v => ?_⟩
  have hv : Matrix.mulVec (((conjAct Q g X : matrixDerived Q) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) v =
        S (Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) (S.symm v)) :=
    matrixConjugation_vector g.val X.val v
  obtain ⟨l, m, hlm⟩ := Submodule.mem_span_pair.1 (hab (S.symm v))
  have hv' : Matrix.mulVec (((conjAct Q g X : matrixDerived Q) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) v - v = S (l • a + m • b) := by
    rw [hv, hlm, map_sub, S.apply_symm_apply]
  rw [hv', map_add, coordinateSemilinearMap_smul, coordinateSemilinearMap_smul]
  exact Submodule.mem_span_pair.2 ⟨_, _, rfl⟩

theorem not_imTwo_of_four {d : ℕ} {A : Matrix (Fin d) (Fin d) K} (v : Fin 4 → Fin d → K)
    (hv : LinearIndependent K v) (y : Fin 4 → Fin d → K)
    (hy : ∀ k, Matrix.mulVec A (y k) - y k = v k ∨ Matrix.mulVec A (y k) - y k = -v k) :
    ¬ImTwo A := by
  classical
  rintro ⟨a, b, hab⟩
  set W := Submodule.span K ({a, b} : Set (Fin d → K))
  have hle : Submodule.span K (Set.range v) ≤ W := by
    refine Submodule.span_le.2 (Set.range_subset_iff.2 fun k => ?_)
    rcases hy k with h | h
    · rw [← h]
      exact hab (y k)
    · rw [← neg_neg (v k), ← h]
      exact W.neg_mem (hab (y k))
  have h4 := finrank_span_eq_card hv
  have h2 : Module.finrank K W ≤ 2 := by
    have h := finrank_span_finset_le_card (R := K) ({a, b} : Finset (Fin d → K))
    rw [Finset.coe_insert, Finset.coe_singleton] at h
    exact h.trans (Finset.card_le_two)
  have := Submodule.finrank_mono hle
  rw [h4, Fintype.card_fin] at this
  omega

section Elements

variable [CharP K 2]

noncomputable abbrev X0 : Om8 K := X8 rootC 1 * X8 rootD 1

theorem theta_X0 [Finite K] : theta (X0 (K := K)) = X8 rootD 1 * X8 rootA 1 := by
  rw [X0, map_mul, theta_X8 rootC_mem, theta_X8 rootD_mem, tri_rootC, tri_rootD]

theorem imTwo_X0 :
    ImTwo ((X0 (K := K) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := by
  refine ⟨AutOm.pvec 0 true + AutOm.pvec 0 false, AutOm.pvec 3 true, fun y => ?_⟩
  refine Submodule.mem_span_pair.2 ⟨polar (coordinateQuadPlus 4 K) y (AutOm.pvec 3 true),
    -(polar (coordinateQuadPlus 4 K) y (AutOm.pvec 0 true) +
      polar (coordinateQuadPlus 4 K) y (AutOm.pvec 0 false) +
      polar (coordinateQuadPlus 4 K) y (AutOm.pvec 3 true)), ?_⟩
  rw [AutOm.mulVec_mul, X8_mulVec (by decide) toStdD_rootD, X8_mulVec (by decide) toStdD_rootC]
  simp only [AutOm.eichlerC, one_smul, AutOm.form_pvec, zero_mul, zero_smul, sub_zero,
    polar_add_left, polar_sub_left, polar_smul_left, AutOm.polar_pvec]
  simp
  module

omit [CharP K 2] in
theorem linearIndependent_four :
    LinearIndependent K ![AutOm.pvec (K := K) (n := 4) 0 true, AutOm.pvec 3 true,
      AutOm.pvec 1 true, AutOm.pvec 2 false] := by
  have hg : Function.Injective (![.inl 0, .inl 3, .inl 1, .inr 2] : Fin 4 → Fin 4 ⊕ Fin 4) := by
    decide
  have h := (Pi.basisFun K (Fin (2 * 4))).linearIndependent.comp _
    ((plusIndexEquiv 4).injective.comp hg)
  convert h using 1
  funext k
  fin_cases k <;> simp [Pi.basisFun_apply, AutOm.pvec_true, AutOm.pvec_false]

noncomputable abbrev mDA : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K :=
  ((X8 rootD 1 * X8 rootA 1 : Om8 K) : GL (Fin (2 * 4)) K)

theorem mDA_mulVec (y : Fin (2 * 4) → K) :
    Matrix.mulVec (mDA (K := K)) y =
      AutOm.eichlerC (coordinateQuadPlus 4 K) (AutOm.pvec 3 true) ((1 : K) • AutOm.pvec 0 true)
        (AutOm.eichlerC (coordinateQuadPlus 4 K) (AutOm.pvec 2 false)
          ((1 : K) • AutOm.pvec 1 true) y) := by
  rw [mDA, AutOm.mulVec_mul, X8_mulVec (by decide) toStdD_rootD,
    X8_mulVec (by decide) toStdD_rootA]

theorem mDA_f3 : Matrix.mulVec (mDA (K := K)) (AutOm.pvec 3 false) - AutOm.pvec 3 false =
    AutOm.pvec 0 true := by
  rw [mDA_mulVec]
  simp only [AutOm.eichlerC, one_smul, AutOm.form_pvec, zero_mul, zero_smul, sub_zero,
    polar_add_left, polar_sub_left, polar_smul_left, AutOm.polar_pvec]
  simp

theorem mDA_f0 : Matrix.mulVec (mDA (K := K)) (AutOm.pvec 0 false) - AutOm.pvec 0 false =
    -AutOm.pvec 3 true := by
  rw [mDA_mulVec]
  simp only [AutOm.eichlerC, one_smul, AutOm.form_pvec, zero_mul, zero_smul, sub_zero,
    polar_add_left, polar_sub_left, polar_smul_left, AutOm.polar_pvec]
  simp

theorem mDA_e2 : Matrix.mulVec (mDA (K := K)) (AutOm.pvec 2 true) - AutOm.pvec 2 true =
    AutOm.pvec 1 true := by
  rw [mDA_mulVec]
  simp only [AutOm.eichlerC, one_smul, AutOm.form_pvec, zero_mul, zero_smul, sub_zero,
    polar_add_left, polar_sub_left, polar_smul_left, AutOm.polar_pvec]
  simp

theorem mDA_f1 : Matrix.mulVec (mDA (K := K)) (AutOm.pvec 1 false) - AutOm.pvec 1 false =
    -AutOm.pvec 2 false := by
  rw [mDA_mulVec]
  simp only [AutOm.eichlerC, one_smul, AutOm.form_pvec, zero_mul, zero_smul, sub_zero,
    polar_add_left, polar_sub_left, polar_smul_left, AutOm.polar_pvec]
  simp

theorem not_imTwo_dA : ¬ImTwo (mDA (K := K)) := by
  refine not_imTwo_of_four _ linearIndependent_four ![AutOm.pvec 3 false, AutOm.pvec 0 false,
    AutOm.pvec 2 true, AutOm.pvec 1 false] fun k => ?_
  fin_cases k
  · exact Or.inl mDA_f3
  · exact Or.inr mDA_f0
  · exact Or.inl mDA_e2
  · exact Or.inr mDA_f1

end Elements

section Outer

variable [CharP K 2] [Finite K]

theorem conjAct_ne_theta (g : similarityPairs (coordinateQuadPlus 4 K)) :
    conjAct _ g ≠ (theta : MulAut (Om8 K)) := by
  intro h
  have h1 := imTwo_conjAct g (imTwo_X0 (K := K))
  rw [h, theta_X0] at h1
  exact not_imTwo_dA h1

theorem conjAct_ne_theta_inv (g : similarityPairs (coordinateQuadPlus 4 K)) :
    conjAct _ g ≠ (theta : MulAut (Om8 K))⁻¹ := by
  intro h
  apply conjAct_ne_theta g⁻¹
  rw [map_inv, h, inv_inv]

theorem theta_sq : (theta : MulAut (Om8 K)) ^ 2 = theta⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← pow_succ, theta_cube]

theorem theta_pow_eq_one_of_eq_conjAct {k : ℕ} {g : similarityPairs (coordinateQuadPlus 4 K)}
    (h : (theta : MulAut (Om8 K)) ^ k = conjAct _ g) : (theta : MulAut (Om8 K)) ^ k = 1 := by
  have hk : (theta : MulAut (Om8 K)) ^ k = theta ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, theta_cube, one_pow, one_mul]
  rw [hk] at h ⊢
  have h3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (k % 3)
  · rfl
  · rw [pow_one] at h
    exact absurd h.symm (conjAct_ne_theta g)
  · rw [theta_sq] at h
    exact absurd h.symm (conjAct_ne_theta_inv g)

end Outer

end Triality

end CFSG.StandardType
