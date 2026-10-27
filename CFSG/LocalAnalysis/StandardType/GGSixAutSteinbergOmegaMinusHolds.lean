module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms

namespace AutOm

section Spin

variable {n : ℕ} {K : Type} [Field K] {b c : K}

noncomputable abbrev ordThreeMinus {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    spinGroup (quadMinus n K b c) :=
  (minusFrame n b c).longSL2 hij s (!t) (upperSL2 1 * lowerSL2 1)

theorem ordThreeMinus_eq {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    ordThreeMinus (b := b) (c := c) hij s t =
      (minusFrame n b c).longRoot hij s (!t) (.ofAdd 1) *
        (minusFrame n b c).longRoot hij (!s) t (.ofAdd (-1)) := by
  rw [ordThreeMinus, map_mul, HypFrame.longSL2_upperSL2, HypFrame.longSL2_lowerSL2,
    Bool.not_not, HypFrame.longRoot_swap (minusFrame n b c).toHypFrame hij.symm t (!s) 1]

theorem commute_ordThreeMinus {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (a : K) :
    Commute ((minusFrame n b c).longRoot hij s t (.ofAdd a)) (ordThreeMinus hij s t) := by
  rw [ordThreeMinus_eq]
  exact ((minusFrame n b c).commute_longRoot_longRoot_left hij hij s t (!t) a 1).mul_right
    ((minusFrame n b c).commute_longRoot_longRoot_right hij hij s t (!s) a (-1))

theorem upper_mul_lower_pow_three [CharP K 2] :
    (upperSL2 (1 : K) * lowerSL2 1) ^ 3 = 1 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul]
  change ((!![(1 : K), 1; 0, 1] * !![(1 : K), 0; 1, 1]) ^ 3) i j =
    (1 : Matrix (Fin 2) (Fin 2) K) i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem spinAction_ordThreeMinus_vec {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    spinAction (quadMinus n K b c) (ordThreeMinus hij s t) ((minusFrame n b c).vec i (!s)) =
      (minusFrame n b c).vec i (!s) - (minusFrame n b c).vec j (!t) := by
  rw [ordThreeMinus_eq, map_mul, LinearEquiv.mul_apply]
  have h1 : spinAction (quadMinus n K b c) ((minusFrame n b c).longRoot hij (!s) t (.ofAdd (-1)))
      ((minusFrame n b c).vec i (!s)) = (minusFrame n b c).vec i (!s) :=
    (minusFrame n b c).spinAction_longRoot_vec_left hij (!s) t (-1)
  rw [h1, (minusFrame n b c).spinAction_longRoot_vec_not_left hij s (!t) 1, one_smul]

theorem ordThreeMinus_ne_one {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    ordThreeMinus (b := b) (c := c) hij s t ≠ 1 := by
  intro h
  have h1 := spinAction_ordThreeMinus_vec (b := b) (c := c) hij s t
  rw [h, map_one] at h1
  have h1' : (minusFrame n b c).vec i (!s) =
      (minusFrame n b c).vec i (!s) - (minusFrame n b c).vec j (!t) := h1
  rw [eq_comm, sub_eq_self] at h1'
  replace h1 := h1'
  have h2 := (minusFrame n b c).polar_vec_not j (!t)
  rw [h1, QuadraticMap.polar_zero_left] at h2
  exact zero_ne_one h2

theorem orderOf_ordThreeMinus [CharP K 2] {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    orderOf (ordThreeMinus (b := b) (c := c) hij s t) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ (ordThreeMinus_ne_one hij s t)
  rw [ordThreeMinus, ← map_pow, upper_mul_lower_pow_three, map_one]

theorem spinAction_ordThreeMinus_z {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) :
    spinAction (quadMinus n K b c) (ordThreeMinus hij s t) (minusFrame n b c).z =
      (minusFrame n b c).z := by
  rw [ordThreeMinus_eq, map_mul, LinearEquiv.mul_apply,
    (minusFrame n b c).spinAction_longRoot_z, (minusFrame n b c).spinAction_longRoot_z]

end Spin

section Good

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn4 : 4 ≤ n) {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

include hirr in
theorem tailRefl_spinModelMinus {x : spinGroup (quadMinus n K b c)}
    (hx : spinAction (quadMinus n K b c) x (planeVec n planeOne) = planeVec n planeOne) :
    tailRefl hn4 (spinModelMinus hn4 hirr x) = spinModelMinus hn4 hirr x := by
  rw [tailRefl_apply_eq_iff hn4 hirr]
  have h := spinModelMinus_mulVec hn4 hirr x (planeVec n planeOne)
  rw [hx, reindex_planeOne] at h
  exact h

include hirr in
theorem goodAut_tailRefl {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool) (a : K) :
    GGGoodAut (spinModelMinus hn4 hirr ((minusFrame n b c).longRoot hij s t (.ofAdd a)))
      (tailRefl hn4) := by
  refine ⟨fun S hfix hS hnorm => eq_bot_of_tailRefl hn4 hirr S hfix hS hnorm, 1, ?_,
    spinModelMinus hn4 hirr (ordThreeMinus hij s t), ?_, ?_, ?_, ?_⟩
  · rw [one_mul, inv_one, mul_one]
    exact tailRefl_spinModelMinus hn4 hirr ((minusFrame n b c).spinAction_longRoot_z hij s t a)
  · exact tailRefl_spinModelMinus hn4 hirr (spinAction_ordThreeMinus_z hij s t)
  · rw [one_mul, inv_one, mul_one, ← map_mul, ← map_mul, (commute_ordThreeMinus hij s t a).eq]
  · intro h
    exact ordThreeMinus_ne_one hij s t
      (spinModelMinus_injective hn4 hirr (h.trans (map_one _).symm))
  · rw [orderOf_injective _ (spinModelMinus_injective hn4 hirr), orderOf_ordThreeMinus]
    decide

include hirr in
theorem autModel_minus {f : ℕ} (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f)
    (R : matrixDerived (Qm n hn4 b c) → Prop)
    (hR : ∀ r, R r → ∃ (i j : Fin (n - 1)) (hij : i ≠ j) (s t : Bool) (a : K)
      (u : spinGroup (quadMinus n K b c)),
        r = spinModelMinus hn4 hirr (u * (minusFrame n b c).longRoot hij s t (.ofAdd a) * u⁻¹)) :
    GGAutModel (matrixDerived (Qm n hn4 b c)) R := by
  refine ⟨inner _, Subgroup.zpowers (frobAut hn4 hirr), inner_normal _, le_rfl, ?_, fun σ => ?_,
    inner_inf_zpowers_frobAut hn4 hirr hf hf1, fun r hr x hx hx2 hx1 e he => ?_⟩
  · rw [show inner (matrixDerived (Qm n hn4 b c)) =
        (MulAut.conj : matrixDerived (Qm n hn4 b c) →* _).range from rfl, Subgroup.relIndex_self]
    exact odd_one
  · obtain ⟨ι, hι, k, rfl⟩ := exists_inner_mul_frobAut_pow hn4 hirr hf σ
    exact ⟨ι, hι, _, Subgroup.npow_mem_zpowers _ k, rfl⟩
  · rw [eq_tailRefl_of_mem_zpowers hn4 hirr hf hf1 hx hx2 hx1]
    refine AutSt.goodAut_conj_inner ?_ he
    obtain ⟨i, j, hij, s, t, a, u, rfl⟩ := hR r hr
    rw [map_mul, map_mul, map_inv]
    exact (goodAut_tailRefl hn4 hirr hij s t a).of_conj _

end Good

end AutOm

section Family

theorem ggAutModelAt_POmegaMinus : GGAutModelAt .POmegaMinus := by
  intro n f hadm _ _
  obtain ⟨-, hf, hn4⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hirr := minusCoeffs_irr 2 f
  refine ⟨matrixDerived (Qm n hn4 (minusCoeffs 2 f).1 (minusCoeffs 2 f).2), inferInstance,
    AutOm.spinModelMinus hn4 hirr, AutOm.spinModelMinus_surjective hn4 hirr,
    AutOm.ker_spinModelMinus hn4 hirr, AutOm.autModel_minus hn4 hirr hK hf _ fun r hr => ?_⟩
  obtain ⟨-, γ, ⟨-, hγl⟩, u, z, hz, rfl⟩ := hr
  obtain ⟨i, j, hij, s, t, hst⟩ :=
    RootCentOmega.exists_long_of_ggLongRoot_minus hirr hn4 (hγl (Or.inr (Or.inl rfl)))
  obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t hst).mp hz
  exact ⟨i, j, hij, s, t, a, u, rfl⟩

theorem ggAutStructureAt_POmegaMinus : GGAutStructureAt .POmegaMinus :=
  ggAutStructureAt_of_autModelAt ggAutModelAt_POmegaMinus

end Family

end CFSG.StandardType
