module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusHolds

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms QuadraticMap

namespace AutOm

section Frame

variable {K : Type} [Field K] {n : ℕ}

noncomputable abbrev pvec (k : Fin n) (r : Bool) : Fin (2 * n) → K :=
  reindexVectorEquiv (plusIndexEquiv n) (plusVec n K k r)

theorem reindex_single {ι : Type} [DecidableEq ι] {d : ℕ} (e : ι ≃ Fin d) (a : ι) :
    reindexVectorEquiv (K := K) e (Pi.single a 1) = Pi.single (e a) 1 := by
  funext k
  rw [reindexVectorEquiv_apply]
  obtain ⟨b, rfl⟩ := e.surjective k
  rw [Equiv.symm_apply_apply]
  by_cases h : b = a
  · subst h
    simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (e.injective.ne h)]

theorem polar_reindex_plus (y z : Fin n ⊕ Fin n → K) :
    polar (coordinateQuadPlus n K) (reindexVectorEquiv (plusIndexEquiv n) y)
        (reindexVectorEquiv (plusIndexEquiv n) z) = polar (quadPlus n K) y z := by
  simp only [polar, ← map_add]
  change reindexQuadraticForm _ _ _ - reindexQuadraticForm _ _ _ - reindexQuadraticForm _ _ _ = _
  rw [reindexQuadraticForm_map, reindexQuadraticForm_map, reindexQuadraticForm_map]

theorem polar_pvec (k l : Fin n) (r t : Bool) :
    polar (coordinateQuadPlus n K) (pvec k r) (pvec l t) = if k = l ∧ r = !t then 1 else 0 := by
  rw [polar_reindex_plus, polar_quadPlus_plusVec]

theorem polar_pvec_not (k : Fin n) (r : Bool) :
    polar (coordinateQuadPlus n K) (pvec k r) (pvec k (!r)) = 1 := by
  rw [polar_pvec, ite_eq_left ⟨rfl, by rw [Bool.not_not]⟩]

theorem polar_pvec_self (k : Fin n) (r : Bool) :
    polar (coordinateQuadPlus n K) (pvec k r) (pvec k r) = 0 := by
  rw [polar_pvec, ite_eq_right]
  rintro ⟨-, h⟩
  cases r <;> simp at h

theorem polar_pvec_of_ne {k l : Fin n} (h : k ≠ l) (r t : Bool) :
    polar (coordinateQuadPlus n K) (pvec k r) (pvec l t) = 0 := by
  rw [polar_pvec, ite_eq_right fun h' => h h'.1]

theorem pvec_true (k : Fin n) :
    (pvec k true : Fin (2 * n) → K) = Pi.single (plusIndexEquiv n (.inl k)) 1 := by
  rw [pvec, plusVec_true, reindex_single]

theorem pvec_false (k : Fin n) :
    (pvec k false : Fin (2 * n) → K) = Pi.single (plusIndexEquiv n (.inr k)) 1 := by
  rw [pvec, plusVec_false, reindex_single]

theorem plusUnitVector_eq [Finite K] [CharP K 2] (hn : 1 ≤ n) :
    CFSG.SeitzReduction.OmegaPilot.plusUnitVector (F := K) hn =
      pvec ⟨0, by omega⟩ true + pvec ⟨0, by omega⟩ false := by
  rw [CFSG.SeitzReduction.OmegaPilot.plusUnitVector, pvec_true, pvec_false, one_smul, one_smul,
    add_zero]

theorem eq_zero_of_polar_pvec {x : Fin (2 * n) → K}
    (hx : ∀ k r, polar (coordinateQuadPlus n K) x (pvec k r) = 0) : x = 0 := by
  obtain ⟨x', rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv n)).surjective x
  rw [RootCentOmega.eq_zero_of_polar_plusVec (x := x') fun k u => by
    rw [polar_comm, ← polar_reindex_plus]
    exact hx k u, map_zero]

theorem eq_top_of_pvec_mem {W : Submodule K (Fin (2 * n) → K)} (h : ∀ k r, pvec k r ∈ W) :
    W = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro y
  rw [← Finset.univ_sum_single y]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [show Pi.single a (y a) = y a • (Pi.single a 1 : Fin (2 * n) → K) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]]
  refine Submodule.smul_mem _ _ ?_
  obtain ⟨b, rfl⟩ := (plusIndexEquiv n).surjective a
  rcases b with k | k
  · rw [← pvec_true]
    exact h k true
  · rw [← pvec_false]
    exact h k false

noncomputable abbrev eich (i j : Fin n) (s t : Bool) (y : Fin (2 * n) → K) : Fin (2 * n) → K :=
  y + (polar (coordinateQuadPlus n K) y (pvec j t)) • pvec i s -
    (polar (coordinateQuadPlus n K) y (pvec i s)) • pvec j t

theorem eich_sub (i j : Fin n) (s t : Bool) (y : Fin (2 * n) → K) :
    eich i j s t y - y = (polar (coordinateQuadPlus n K) y (pvec j t)) • pvec i s -
      (polar (coordinateQuadPlus n K) y (pvec i s)) • pvec j t := by
  rw [eich]
  abel

theorem spread (W : Submodule K (Fin (2 * n) → K)) (P : Fin n → Prop)
    (hW : ∀ (i j : Fin n), i ≠ j → ∀ s t : Bool, P i → P j → ∀ y ∈ W, eich i j s t y ∈ W)
    (h3 : ∀ a b : Fin n, ∃ c, P c ∧ c ≠ a ∧ c ≠ b) {x : Fin (2 * n) → K} (hx : x ∈ W)
    {k : Fin n} {r : Bool} (hk : P k)
    (hxk : polar (coordinateQuadPlus n K) x (pvec k r) ≠ 0) :
    ∀ m u, P m → pvec m u ∈ W := by
  have hsub : ∀ (i j : Fin n), i ≠ j → ∀ s t : Bool, P i → P j → ∀ y ∈ W,
      (polar (coordinateQuadPlus n K) y (pvec j t)) • pvec i s -
        (polar (coordinateQuadPlus n K) y (pvec i s)) • pvec j t ∈ W := by
    intro i j hij s t hi hj y hy
    rw [← eich_sub]
    exact W.sub_mem (hW i j hij s t hi hj y hy) hy
  obtain ⟨l, hl, hlk, -⟩ := h3 k k
  obtain ⟨m₀, hm₀, hmk, hml⟩ := h3 k l
  set y₁ := (polar (coordinateQuadPlus n K) x (pvec k r)) • (pvec l true : Fin (2 * n) → K) -
    (polar (coordinateQuadPlus n K) x (pvec l true)) • pvec k r with hy₁
  have hy₁W : y₁ ∈ W := hsub l k hlk true r hl hk x hx
  have hm₀W : ∀ u, pvec m₀ u ∈ W := by
    intro u
    have h := hsub m₀ l hml u false hm₀ hl y₁ hy₁W
    have e1 : polar (coordinateQuadPlus n K) y₁ (pvec l false) =
        polar (coordinateQuadPlus n K) x (pvec k r) := by
      rw [hy₁, polar_sub_left, polar_smul_left, polar_smul_left, polar_pvec, polar_pvec]
      simp [hlk.symm]
    have e2 : polar (coordinateQuadPlus n K) y₁ (pvec m₀ u) = 0 := by
      rw [hy₁, polar_sub_left, polar_smul_left, polar_smul_left, polar_pvec, polar_pvec]
      simp [hml.symm, hmk.symm]
    rw [e1, e2, zero_smul, sub_zero] at h
    have := W.smul_mem (polar (coordinateQuadPlus n K) x (pvec k r))⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hxk, one_smul] at this
  intro m u hm
  by_cases hmm : m = m₀
  · subst hmm
    exact hm₀W u
  · have h := hsub m m₀ hmm u false hm hm₀ (pvec m₀ true) (hm₀W true)
    rw [polar_pvec, polar_pvec] at h
    simpa [Ne.symm hmm] using h

end Frame

section Model

variable {K : Type} [Field K] {n : ℕ}

theorem spinModelPlus_longRoot_mulVec (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (c : K) (y : Fin (2 * n) → K) :
    Matrix.mulVec ((spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd c)) :
        GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) y =
      y + (c * polar (coordinateQuadPlus n K) y (pvec j t)) • pvec i s -
        (c * polar (coordinateQuadPlus n K) y (pvec i s)) • pvec j t := by
  obtain ⟨y', rfl⟩ := (reindexVectorEquiv (K := K) (plusIndexEquiv n)).surjective y
  rw [spinModelPlus_mulVec, HypFrame.spinAction_longRoot, plusFrame_vec, map_sub, map_add,
    LinearEquiv.map_smul, LinearEquiv.map_smul, polar_reindex_plus, polar_reindex_plus]

end Model

section Fixed

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem conjAct_apply_eq_self_iff (g : similarityPairs Q) (X : matrixDerived Q) :
    conjAct Q g X = X ↔ ∀ y, coordinateSemilinearMap g.val
        (Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y) =
      Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (coordinateSemilinearMap g.val y) := by
  have hval : ∀ v, Matrix.mulVec (((conjAct Q g X : matrixDerived Q) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) v = coordinateSemilinearMap g.val
        (Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
          ((coordinateSemilinearMap g.val).symm v)) := fun v =>
    matrixConjugation_vector g.val X.val v
  constructor
  · intro h y
    have := hval (coordinateSemilinearMap g.val y)
    rw [h, AddEquiv.symm_apply_apply] at this
    exact this.symm
  · intro h
    apply Subtype.ext
    apply Units.ext
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hval, h, AddEquiv.apply_symm_apply]

theorem coordinateSemilinearMap_inclusion (B : matrixIsometries Q) (y : Fin d → K) :
    coordinateSemilinearMap (matrixIsometryInclusion Q B).val y =
      Matrix.mulVec ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y := by
  rw [matrixIsometryInclusion_val, coordinateSemilinearMap_inl, matrixLinearEquiv_apply]

variable [Finite K] [CharP K 2]

theorem exists_fixed_ne_zero (hd : 1 ≤ d) (S : Subgroup (matrixDerived Q)) (hS : IsPGroup 2 S) :
    ∃ x : Fin d → K, x ≠ 0 ∧ ∀ q ∈ S,
      Matrix.mulVec (((q : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) x = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S (Fin d → K) :=
    { smul := fun q x => Matrix.mulVec
        (((q : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) x
      one_smul := fun x => Matrix.one_mulVec x
      mul_smul := fun q q' x => by
        change Matrix.mulVec ((((q * q' : S) : matrixDerived Q) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) x = Matrix.mulVec
            (((q : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (Matrix.mulVec (((q' : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) x)
        rw [Matrix.mulVec_mulVec]
        rfl }
  have h2 : 2 ∣ Nat.card (Fin d → K) := by
    rw [Nat.card_fun, Nat.card_fin]
    exact dvd_pow two_dvd_card (by omega)
  have h0 : (0 : Fin d → K) ∈ MulAction.fixedPoints S (Fin d → K) := fun q =>
    Matrix.mulVec_zero _
  obtain ⟨b, hb, hne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ h2 h0
  exact ⟨b, fun h => hne h.symm, fun q hq => hb ⟨q, hq⟩⟩

omit [Finite K] [CharP K 2] in
theorem eq_bot_of_fix_top (S : Subgroup (matrixDerived Q))
    (h : ∀ q ∈ S, ∀ y, Matrix.mulVec (((q : matrixDerived Q) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) y = y) : S = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro q hq
  apply Subtype.ext
  apply Units.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h q hq]
  simp

end Fixed

end AutOm

end CFSG.StandardType
