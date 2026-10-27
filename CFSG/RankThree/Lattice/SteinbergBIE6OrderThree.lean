module

public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIPoly

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 RootSpace Polynomial

@[expose] def e6T3Word : List (Fin 6) := [0, 1, 2, 3, 4, 5]

@[expose] def e6T3W : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word e6T3Word) ^ 4

@[expose] def e6T3MList : List (List ℤ) :=
  [[0, 0, 0, 0, 0, -1], [1, 0, 0, 0, -1, 0], [1, 1, 0, -1, 0, -1], [1, 1, 1, -1, -1, -1],
    [1, 1, 0, 0, -1, -1], [1, 0, 0, 0, 0, -1]]

@[expose] def e6T3Supports : List (Finset (Fin Tag.E6.rank)) :=
  [∅, {0, 2}, {1, 3}, {2, 3}, {3, 4}, {4, 5}, {0, 2, 4, 5}, {1, 2, 3, 4}]

@[expose] def e6T3Pairs : List (Fin Tag.E6.rank × Fin Tag.E6.rank) :=
  [(0, 2), (1, 3), (2, 3), (3, 4), (4, 5)]

theorem e6T3W_eq_wordProd : e6T3W = (coxeterSystem Tag.E6).wordProd
    (e6Word e6T3Word ++ e6Word e6T3Word ++ e6Word e6T3Word ++ e6Word e6T3Word) := by
  simp only [e6T3W, pow_succ, pow_zero, one_mul, CoxeterSystem.wordProd_append]

theorem weylMatrix_e6T3W : weylMatrix e6T3W = toMat Tag.E6.rank e6T3MList := by
  rw [e6T3W_eq_wordProd]
  exact weylMatrix_wordProd_e6 (ω := e6T3Word ++ e6T3Word ++ e6T3Word ++ e6T3Word)
    (by decide +kernel)

theorem e6T3_sq : toMat Tag.E6.rank e6T3MList * toMat Tag.E6.rank e6T3MList +
    toMat Tag.E6.rank e6T3MList + 1 = 0 := by
  rw [← toMat_lmul, ← toMat_ladd, ← toMat_lid, ← toMat_ladd, ← toMat_lzero]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem e6T3_cube : e6T3W ^ 3 = 1 := by
  apply weylMatrix_injective
  rw [weylMatrix_pow, weylMatrix_e6T3W, weylMatrix_one, ← toMat_lpow, ← toMat_lid]
  exact congrArg (toMat Tag.E6.rank) (by decide +kernel)

theorem weyl_smul_add (g : WeylGroup Tag.E6) (x y : Fin Tag.E6.rank → ℤ) :
    g • (x + y) = g • x + g • y := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, ← weylMatrix_mulVec, Matrix.mulVec_add]

theorem weyl_smul_zero (g : WeylGroup Tag.E6) : g • (0 : Fin Tag.E6.rank → ℤ) = 0 := by
  rw [← weylMatrix_mulVec, Matrix.mulVec_zero]

theorem e6T3_lattice (x : Fin Tag.E6.rank → ℤ) : e6T3W • e6T3W • x + e6T3W • x + x = 0 := by
  rw [← weylMatrix_mulVec, ← weylMatrix_mulVec, weylMatrix_e6T3W,
    Matrix.mulVec_mulVec, ← Matrix.add_mulVec, ← Matrix.one_mulVec x, Matrix.mulVec_mulVec,
    Matrix.mul_one, ← Matrix.add_mulVec, e6T3_sq, Matrix.zero_mulVec]

theorem e6T3_real (y : RootSpace Tag.E6) :
    weylAct Tag.E6 e6T3W (weylAct Tag.E6 e6T3W y) + weylAct Tag.E6 e6T3W y + y = 0 := by
  have key : ∀ i, weylAct Tag.E6 e6T3W (weylAct Tag.E6 e6T3W (ofLattice (Pi.single i 1))) +
      weylAct Tag.E6 e6T3W (ofLattice (Pi.single i 1)) + ofLattice (Pi.single i 1) = 0 := by
    intro i
    rw [weylAct_ofLattice, weylAct_ofLattice, ← ofLattice_add, ← ofLattice_add, e6T3_lattice,
      ofLattice_zero]
  conv_lhs => rw [← sum_smul_ofLattice_single y]
  simp only [map_sum, map_smul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [← smul_add, ← smul_add, key, smul_zero]

theorem e6T3_real_fixed {y : RootSpace Tag.E6} (h : weylAct Tag.E6 e6T3W y = y) : y = 0 := by
  have h3 := e6T3_real y
  rw [h, h] at h3
  have : (3 : ℝ) • y = 0 := by rw [← h3]; module
  exact (smul_eq_zero.1 this).resolve_left (by norm_num)

theorem e6T3_lattice_fixed {x : Fin Tag.E6.rank → ℤ} (h : e6T3W • x = x) : x = 0 := by
  have h3 := e6T3_lattice x
  rw [h, h] at h3
  funext i
  have := congrFun h3 i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  rw [Pi.zero_apply]
  omega

theorem weylMatrix_sq_add_of_smul {T : WeylGroup Tag.E6}
    (hT : ∀ x : Fin Tag.E6.rank → ℤ, T • T • x + T • x + x = 0) :
    weylMatrix T * weylMatrix T + weylMatrix T + 1 = 0 := by
  ext i j
  have h := congrFun (hT (Pi.single j 1)) i
  rw [Matrix.add_apply, Matrix.add_apply, ← weylMatrix_mul, weylMatrix_apply, weylMatrix_apply,
    mul_smul, Matrix.one_apply, Matrix.zero_apply]
  simp only [Pi.add_apply, Pi.zero_apply, Pi.single_apply] at h
  exact h

theorem e6T3_supports_complete : ∀ S : Finset (Fin Tag.E6.rank), S ≠ Finset.univ →
    S.card % 2 = 0 →
    (Finset.univ.filter fun m : Fin 72 => ∀ i, i ∉ S → e6RootVec m i = 0).card % 3 = 0 →
    S ∈ e6T3Supports := by
  decide +kernel

theorem e6T3_parabolic_card (S : Finset (Fin Tag.E6.rank)) :
    (parabolicRoots Tag.E6 ↑S).ncard =
      (Finset.univ.filter fun m : Fin 72 => ∀ i, i ∉ S → e6RootVec m i = 0).card :=
  ncard_parabolicRoots_eq (P := fun i => i ∈ S) (fun _ => Finset.mem_coe) rfl

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem E6_order_three_Weyl_lattice_and_seven_root_kernels [Fintype (WeylGroup Tag.E6)] :
    Nat.card (WeylGroup Tag.E6) = 51840 ∧
    ∑ a : WeylGroup Tag.E6, (X : ℤ[X]) ^ (coxeterSystem Tag.E6).length a =
      (([2, 5, 6, 8, 9, 12] : List ℕ).map fun d => ∑ i ∈ Finset.range d, (X : ℤ[X]) ^ i).prod ∧
    ((([2, 5, 6, 8, 9, 12] : List ℕ).map fun d =>
      ∑ i ∈ Finset.range d, (X : ℤ[X]) ^ i).prod).eval 2 = 3126356394525 ∧
    padicValNat 7 3126356394525 = 3 ∧
    weylMatrix e6T3W = !![0, 0, 0, 0, 0, -1; 1, 0, 0, 0, -1, 0; 1, 1, 0, -1, 0, -1;
      1, 1, 1, -1, -1, -1; 1, 1, 0, 0, -1, -1; 1, 0, 0, 0, 0, -1] ∧
    weylMatrix e6T3W ^ 2 + weylMatrix e6T3W + 1 = 0 ∧
    (∀ v : Fin Tag.E6.rank → ZMod 7, v ≠ 0 →
      (∀ a : WeylGroup Tag.E6, (dualMatrix (ZMod 7) a⁻¹).mulVec v = v ↔
        a ∈ Subgroup.closure {s | ∃ α ∈ rootKernel v, s = rootReflection α}) ∧
      (∃ u : WeylGroup Tag.E6, ∃ J : Set (Fin Tag.E6.rank), J ≠ Set.univ ∧
        (u • ·) '' rootKernel v = parabolicRoots Tag.E6 J) ∧
      ((dualMatrix (ZMod 7) e6T3W).mulVec v = (2 : ZMod 7) • v →
        ∃ u : WeylGroup Tag.E6, ∃ S ∈ e6T3Supports,
          (u • ·) '' rootKernel v = parabolicRoots Tag.E6 ↑S ∧
          ∀ x ∈ Submodule.span ℝ (ofLattice '' parabolicRoots Tag.E6 ↑S),
            weylAct Tag.E6 (u * e6T3W * u⁻¹) x = x → x = 0)) ∧
    (parabolicRoots Tag.E6 ↑(∅ : Finset (Fin Tag.E6.rank))).ncard = 0 ∧
    (∀ ab ∈ e6T3Pairs,
      (parabolicRoots Tag.E6 ↑({ab.1, ab.2} : Finset (Fin Tag.E6.rank))).ncard = 6 ∧
      (Matrix.of fun i j : Fin 2 => Tag.E6.cartan (![ab.1, ab.2] i) (![ab.1, ab.2] j)) =
        !![2, -1; -1, 2]) ∧
    (parabolicRoots Tag.E6 ↑({0, 2, 4, 5} : Finset (Fin Tag.E6.rank))).ncard = 12 ∧
    (Matrix.of fun i j : Fin 4 => Tag.E6.cartan (![0, 2, 4, 5] i) (![0, 2, 4, 5] j)) =
      !![2, -1, 0, 0; -1, 2, 0, 0; 0, 0, 2, -1; 0, 0, -1, 2] ∧
    (parabolicRoots Tag.E6 ↑({1, 2, 3, 4} : Finset (Fin Tag.E6.rank))).ncard = 24 ∧
    ∀ i j : Fin Tag.D4.rank,
      Tag.E6.cartan (![1, 2, 3, 4] i) (![1, 2, 3, 4] j) = Tag.D4.cartan i j := by
  obtain ⟨hpoly, hcard⟩ := CFSG.RankThree.Chevalley.E6_weyl_length_polynomial
  have hsq : weylMatrix e6T3W * weylMatrix e6T3W + weylMatrix e6T3W + 1 = 0 := by
    rw [weylMatrix_e6T3W]
    exact e6T3_sq
  refine ⟨hcard, hpoly, ?_, ?_, ?_, by rw [sq]; exact hsq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, eval_mul,
      eval_finsetSum, eval_pow, eval_X, mul_one]
    decide
  · rw [show (3126356394525 : ℕ) = 7 ^ 3 * 9114741675 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  · rw [weylMatrix_e6T3W]
    show toMat 6 e6T3MList = _
    decide +kernel
  · intro v hv
    obtain ⟨u₀, J₀, hΦ₀, hJ₀⟩ := exists_smul_rootKernel_eq_parabolicRoots (by norm_num) v
    refine ⟨fun a => ?_, ⟨u₀, J₀, hJ₀ hv, hΦ₀⟩, fun hw2 => ?_⟩
    · rw [← mem_dualWeylStabilizer_iff_dualMatrix, dualWeylStabilizer_eq_closure (by norm_num)]
    have hmaps : ∀ α ∈ rootKernel v, e6T3W • α ∈ rootKernel v := fun α hα =>
      ⟨IsRoot.smul hα.1 e6T3W, by
        rw [← charVal_dualMatrix, hw2, charVal_smul_col, hα.2, mul_zero]⟩
    set T := u₀ * e6T3W * u₀⁻¹ with hTdef
    have hTmaps : ∀ β ∈ parabolicRoots Tag.E6 J₀, T • β ∈ parabolicRoots Tag.E6 J₀ := by
      intro β hβ
      rw [← hΦ₀] at hβ ⊢
      obtain ⟨α, hα, rfl⟩ := hβ
      exact ⟨e6T3W • α, hmaps α hα, by rw [hTdef, mul_smul, mul_smul, inv_smul_smul]⟩
    have hTlat : ∀ x : Fin Tag.E6.rank → ℤ, T • T • x + T • x + x = 0 := by
      intro x
      obtain ⟨y, rfl⟩ : ∃ y, x = u₀ • y := ⟨u₀⁻¹ • x, (smul_inv_smul u₀ x).symm⟩
      simp only [hTdef, mul_smul, inv_smul_smul]
      rw [← weyl_smul_add, ← weyl_smul_add, e6T3_lattice, weyl_smul_zero]
    classical
    have heven : J₀.toFinset.card % 2 = 0 := by
      have h := even_card_of_sq_add_self_add_one (weylMatrix_sq_add_of_smul hTlat) J₀.toFinset
        fun a ha c hc => by
          rw [Set.mem_toFinset] at ha hc
          rw [weylMatrix_apply]
          exact (hTmaps _ (single_mem_parabolicRoots_E6 hc)).2 a ha
      exact Nat.even_iff.1 h
    have hfin : (rootKernel v).Finite := (finite_setOf_isRoot Tag.E6).subset fun α hα => hα.1
    have h3 : 3 ∣ (rootKernel v).ncard :=
      three_dvd_ncard_of_free hfin e6T3_cube hmaps fun α hα h =>
        (IsRoot.ne_zero hα.1) (e6T3_lattice_fixed h)
    have hcardΦ : (parabolicRoots Tag.E6 J₀).ncard = (rootKernel v).ncard := by
      rw [← hΦ₀]
      exact Set.ncard_image_of_injective _ (MulAction.injective u₀)
    have hJ' : (J₀.toFinset : Set (Fin Tag.E6.rank)) = J₀ := Set.coe_toFinset J₀
    have hS : J₀.toFinset ∈ e6T3Supports := by
      refine e6T3_supports_complete _ (fun h => hJ₀ hv ?_) heven ?_
      · rw [← hJ', h, Finset.coe_univ]
      · rw [← e6T3_parabolic_card, hJ', hcardΦ]
        exact Nat.mod_eq_zero_of_dvd h3
    refine ⟨u₀, J₀.toFinset, hS, by rw [hJ']; exact hΦ₀, fun x _ hx => ?_⟩
    have hx' : weylAct Tag.E6 e6T3W (weylAct Tag.E6 u₀⁻¹ x) = weylAct Tag.E6 u₀⁻¹ x := by
      have := congrArg (weylAct Tag.E6 u₀⁻¹) hx
      rwa [weylAct_mul_apply, weylAct_mul_apply, ← weylAct_mul_apply u₀⁻¹ u₀,
        inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id] at this
    have h0 := e6T3_real_fixed hx'
    have := congrArg (weylAct Tag.E6 u₀) h0
    rwa [← weylAct_mul_apply, mul_inv_cancel, map_one, LinearIsometryEquiv.coe_one, id,
      map_zero] at this
  · rw [e6T3_parabolic_card]
    decide +kernel
  · intro ab hab
    simp only [e6T3Pairs, List.mem_cons, List.not_mem_nil, or_false] at hab
    rcases hab with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by rw [e6T3_parabolic_card]; decide +kernel, by decide +kernel⟩
  · rw [e6T3_parabolic_card]
    decide +kernel
  · decide +kernel
  · rw [e6T3_parabolic_card]
    decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel

end CFSG.RankThree.Lattice
