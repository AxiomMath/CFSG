module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusOTwo
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinusHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

namespace AutOm

section Spin

variable {n : ℕ} {K : Type} [Field K]

noncomputable abbrev ordThreePlus (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    spinGroup (quadPlus n K) :=
  (plusFrame n K hn).longSL2 hij s (!t) (upperSL2 1 * lowerSL2 1)

theorem ordThreePlus_eq (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    ordThreePlus (K := K) hn hij s t =
      (plusFrame n K hn).longRoot hij s (!t) (.ofAdd 1) *
        (plusFrame n K hn).longRoot hij (!s) t (.ofAdd (-1)) := by
  rw [ordThreePlus, map_mul, HypFrame.longSL2_upperSL2, HypFrame.longSL2_lowerSL2,
    Bool.not_not, HypFrame.longRoot_swap (plusFrame n K hn) hij.symm t (!s) 1]

theorem commute_ordThreePlus (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) (a : K) :
    Commute ((plusFrame n K hn).longRoot hij s t (.ofAdd a)) (ordThreePlus hn hij s t) := by
  rw [ordThreePlus_eq]
  exact ((plusFrame n K hn).commute_longRoot_longRoot_left hij hij s t (!t) a 1).mul_right
    ((plusFrame n K hn).commute_longRoot_longRoot_right hij hij s t (!s) a (-1))

theorem ordThreePlus_ne_one (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    ordThreePlus (K := K) hn hij s t ≠ 1 := by
  intro h
  have h1 : spinAction (quadPlus n K) (ordThreePlus hn hij s t) ((plusFrame n K hn).vec i (!s)) =
      (plusFrame n K hn).vec i (!s) - (plusFrame n K hn).vec j (!t) := by
    rw [ordThreePlus_eq, map_mul, LinearEquiv.mul_apply,
      (plusFrame n K hn).spinAction_longRoot_vec_left hij (!s) t (-1),
      (plusFrame n K hn).spinAction_longRoot_vec_not_left hij s (!t) 1, one_smul]
  rw [h, map_one] at h1
  have h1' : (plusFrame n K hn).vec i (!s) =
      (plusFrame n K hn).vec i (!s) - (plusFrame n K hn).vec j (!t) := h1
  rw [eq_comm, sub_eq_self] at h1'
  have h2 := (plusFrame n K hn).polar_vec_not j (!t)
  rw [h1', QuadraticMap.polar_zero_left] at h2
  exact zero_ne_one h2

theorem orderOf_ordThreePlus [CharP K 2] (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    orderOf (ordThreePlus (K := K) hn hij s t) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ (ordThreePlus_ne_one hn hij s t)
  rw [ordThreePlus, ← map_pow, upper_mul_lower_pow_three, map_one]

theorem ordThreePlus_eq_one [CharP K 2] (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    ordThreePlus (K := K) hn hij s t =
      (plusFrame n K hn).longRoot hij s (!t) (.ofAdd 1) *
        (plusFrame n K hn).longRoot hij (!s) t (.ofAdd 1) := by
  rw [ordThreePlus_eq, CharTwo.neg_eq]

end Spin

section Normalize

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_torus_conj_one (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) {a : K}
    (ha : a ≠ 0) : ∃ g : spinGroup (quadPlus n K),
      g * (plusFrame n K hn).longRoot hij s t (.ofAdd a) * g⁻¹ =
        (plusFrame n K hn).longRoot hij s t (.ofAdd 1) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a⁻¹
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hr
    exact inv_ne_zero ha hr
  refine ⟨(plusFrame n K hn).longTorus hij s t (Units.mk0 r hr0), ?_⟩
  rw [HypFrame.longTorus_conj_longRoot]
  have hc : longCoroot i j s t i s + longCoroot i j s t j t = 2 := by
    simp [longCoroot, hij, hij.symm]
  rw [hc, zpow_two, Units.val_mul, Units.val_mk0, ← hr, inv_mul_cancel₀ ha]

omit [Finite K] in
theorem longWeylSign_charTwo {i m : Fin n} : (longWeylSign i m : K) = 1 := by
  unfold longWeylSign
  split_ifs
  · exact CharTwo.neg_eq 1
  · rfl

theorem exists_conj_longRoot_one (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) {a : K}
    (ha : a ≠ 0) :
    ∃ (g : spinGroup (quadPlus n K)) (i' j' : Fin n) (hij' : i' ≠ j') (s' t' : Bool),
      i' ≠ ⟨0, by omega⟩ ∧ j' ≠ ⟨0, by omega⟩ ∧
        g * (plusFrame n K hn).longRoot hij s t (.ofAdd a) * g⁻¹ =
          (plusFrame n K hn).longRoot hij' s' t' (.ofAdd 1) := by
  obtain ⟨h, hh⟩ := exists_torus_conj_one hn hij s t ha
  set z : Fin n := ⟨0, by omega⟩ with hz
  by_cases hi : i = z
  · subst hi
    obtain ⟨k, hk0, hkj⟩ := exists_ne_and_ne hn z j
    have h0k : z ≠ k := Ne.symm hk0
    have hj : j ≠ z := Ne.symm hij
    refine ⟨(plusFrame n K hn).longWeyl h0k true true * h, Equiv.swap z k z, Equiv.swap z k j,
      (Equiv.swap z k).injective.ne hij, longWeylBool z k true true z s,
      longWeylBool z k true true j t, ?_, ?_, ?_⟩
    · rw [Equiv.swap_apply_left]
      exact hk0
    · rw [Equiv.swap_apply_of_ne_of_ne hj (Ne.symm hkj)]
      exact hj
    · have e : (plusFrame n K hn).longWeyl h0k true true * h *
          (plusFrame n K hn).longRoot hij s t (.ofAdd a) *
            ((plusFrame n K hn).longWeyl h0k true true * h)⁻¹ =
          (plusFrame n K hn).longWeyl h0k true true *
            (h * (plusFrame n K hn).longRoot hij s t (.ofAdd a) * h⁻¹) *
              ((plusFrame n K hn).longWeyl h0k true true)⁻¹ := by group
      rw [e, hh, HypFrame.longWeyl_conj_longRoot, longWeylSign_charTwo, longWeylSign_charTwo,
        one_mul, one_mul]
  · by_cases hj : j = z
    · subst hj
      obtain ⟨k, hk0, hki⟩ := exists_ne_and_ne hn z i
      have h0k : z ≠ k := Ne.symm hk0
      refine ⟨(plusFrame n K hn).longWeyl h0k true true * h, Equiv.swap z k i, Equiv.swap z k z,
        (Equiv.swap z k).injective.ne hij, longWeylBool z k true true i s,
        longWeylBool z k true true z t, ?_, ?_, ?_⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hi (Ne.symm hki)]
        exact hi
      · rw [Equiv.swap_apply_left]
        exact hk0
      · have e : (plusFrame n K hn).longWeyl h0k true true * h *
            (plusFrame n K hn).longRoot hij s t (.ofAdd a) *
              ((plusFrame n K hn).longWeyl h0k true true * h)⁻¹ =
            (plusFrame n K hn).longWeyl h0k true true *
              (h * (plusFrame n K hn).longRoot hij s t (.ofAdd a) * h⁻¹) *
                ((plusFrame n K hn).longWeyl h0k true true)⁻¹ := by group
        rw [e, hh, HypFrame.longWeyl_conj_longRoot, longWeylSign_charTwo, longWeylSign_charTwo,
          one_mul, one_mul]
    · exact ⟨h, i, j, hij, s, t, hi, hj, hh⟩

end Normalize

section Good

open CFSG.SeitzReduction

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem goodAut_plus_of (hn : 3 ≤ n) {c : MulAut (matrixDerived (coordinateQuadPlus n K))}
    (hO : ∀ S : Subgroup (matrixDerived (coordinateQuadPlus n K)), (∀ q ∈ S, c q = q) →
      IsPGroup 2 S → (∀ y, c y = y → ∀ q ∈ S, y * q * y⁻¹ ∈ S) → S = ⊥)
    (hfix : ∀ (i j : Fin n) (hij : i ≠ j) (s t : Bool), i ≠ ⟨0, by omega⟩ → j ≠ ⟨0, by omega⟩ →
      c (spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd 1))) =
        spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd 1)))
    {r : matrixDerived (coordinateQuadPlus n K)} (hr : PlusRootElt hn r) : GGGoodAut r c := by
  have key : ∀ (i' j' : Fin n) (hij' : i' ≠ j') (s' t' : Bool), i' ≠ ⟨0, by omega⟩ →
      j' ≠ ⟨0, by omega⟩ →
        GGGoodAut (spinModelPlus hn ((plusFrame n K hn).longRoot hij' s' t' (.ofAdd 1))) c := by
    intro i' j' hij' s' t' hi' hj'
    have hy : c (spinModelPlus hn (ordThreePlus hn hij' s' t')) =
        spinModelPlus hn (ordThreePlus hn hij' s' t') := by
      rw [ordThreePlus_eq_one, map_mul, map_mul, hfix i' j' hij' s' (!t') hi' hj',
        hfix i' j' hij' (!s') t' hi' hj']
    refine ⟨hO, 1, ?_, spinModelPlus hn (ordThreePlus hn hij' s' t'), hy, ?_, ?_, ?_⟩
    · rw [one_mul, inv_one, mul_one]
      exact hfix i' j' hij' s' t' hi' hj'
    · rw [one_mul, inv_one, mul_one, ← map_mul, ← map_mul,
        (commute_ordThreePlus hn hij' s' t' 1).eq]
    · intro h
      exact ordThreePlus_ne_one hn hij' s' t'
        (spinModelPlus_injective hn (h.trans (map_one _).symm))
    · rw [orderOf_injective _ (spinModelPlus_injective hn), orderOf_ordThreePlus]
      decide
  obtain ⟨i, j, hij, s, t, a, u, rfl⟩ := hr
  by_cases ha : a = 0
  · subst ha
    have h1 : (plusFrame n K hn).longRoot hij s t (.ofAdd 0) = 1 := by
      rw [ofAdd_zero, map_one]
    have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
    obtain ⟨hO', -, -, y, hy, -, hy1, hyo⟩ :=
      key ⟨1, by omega⟩ ⟨2, by omega⟩ h12 true true (by simp [Fin.ext_iff])
        (by simp [Fin.ext_iff])
    rw [h1, mul_one, mul_inv_cancel, map_one]
    exact ⟨hO', 1, by simp, y, hy, by simp, hy1, hyo⟩
  · obtain ⟨g, i', j', hij', s', t', hi', hj', hg⟩ := exists_conj_longRoot_one hn hij s t ha
    have h := (key i' j' hij' s' t' hi' hj').of_conj (spinModelPlus hn (u * g⁻¹))
    have e : spinModelPlus hn (u * (plusFrame n K hn).longRoot hij s t (.ofAdd a) * u⁻¹) =
        spinModelPlus hn (u * g⁻¹) *
          spinModelPlus hn ((plusFrame n K hn).longRoot hij' s' t' (.ofAdd 1)) *
            (spinModelPlus hn (u * g⁻¹))⁻¹ := by
      rw [← hg, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    rw [e]
    exact h

theorem plusGoodInput_holds : PlusGoodInput := by
  intro K _ _ _ n hn5
  refine ⟨fun r hr => goodAut_plus_of (by omega) (eq_bot_of_plusRefl (by omega))
    (fun i j hij s t hi hj => plusRefl_fix_longRoot (by omega) hij hi hj s t 1) hr,
    fun σ hσσ hσ1 r hr => ⟨?_, ?_⟩⟩
  · exact goodAut_plus_of (by omega)
      (fun S _ hS hnorm => eq_bot_of_fieldAutP (by omega) σ S hS hnorm)
      (fun i j hij s t _ _ => fieldAutP_fix_longRoot (by omega) σ hij s t) hr
  · exact goodAut_plus_of (by omega)
      (fun S _ hS hnorm => eq_bot_of_reflFieldAutP (by omega) hσσ hσ1 S hS hnorm)
      (fun i j hij s t hi hj => reflField_fix_longRoot (by omega) σ hij hi hj s t) hr

end Good

end AutOm

section Family

theorem ggAutModelAt_POmegaPlus_of_four (h4 : GGAutModelPlusFourInput) :
    GGAutModelAt .POmegaPlus :=
  ggAutModelAt_POmegaPlus_of_inputs h4 AutOm.plusGoodInput_holds

theorem ggAutStructureAt_POmegaPlus_of_four (h4 : GGAutModelPlusFourInput) :
    GGAutStructureAt .POmegaPlus :=
  ggAutStructureAt_of_autModelAt (ggAutModelAt_POmegaPlus_of_four h4)

end Family

end CFSG.StandardType
