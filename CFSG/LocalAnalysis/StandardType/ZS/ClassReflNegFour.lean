module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.LocalAnalysis.StandardType.GGWitOrthPolar
import CFSG.LocalAnalysis.StandardType.ZS.OrthReflect

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def negFourForm [Fact (Nat.Prime 5)] (c : ZMod 5) :
    QuadraticForm (ZMod 5) (Fin 4 → ZMod 5) :=
  QuadraticMap.weightedSumSquares (ZMod 5) (fun _ : Fin 4 => c)

private lemma negFourForm_apply [Fact (Nat.Prime 5)] (c : ZMod 5) (x : Fin 4 → ZMod 5) :
    negFourForm c x = c * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) := by
  rw [negFourForm, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_four]
  ring

private lemma negFourForm_apply_single [Fact (Nat.Prime 5)] (c : ZMod 5) (i : Fin 4) :
    negFourForm c (Pi.single i 1) = c := by
  rw [negFourForm_apply]
  fin_cases i <;> simp [Pi.single_apply]

private lemma negFourForm_polar_single [Fact (Nat.Prime 5)] (c : ZMod 5)
    {i j : Fin 4} (hij : i ≠ j) :
    QuadraticMap.polar (negFourForm c) (Pi.single i 1) (Pi.single j 1) = 0 := by
  rw [negFourForm, owPo_polar_weightedSumSquares]
  have hterm : ∀ k, c * ((Pi.single i 1 : Fin 4 → ZMod 5) k *
      (Pi.single j 1 : Fin 4 → ZMod 5) k) = 0 := by
    intro k
    by_cases hki : k = i
    · rw [hki, Pi.single_eq_same, Pi.single_apply, if_neg hij, mul_zero, mul_zero]
    · simp [Pi.single_apply, hki]
  rw [Finset.sum_eq_zero (fun k _ => hterm k), mul_zero]

private lemma negFourForm_polar_nondegenerate [Fact (Nat.Prime 5)] (c : ZMod 5) (hc : c ≠ 0) :
    (QuadraticMap.polarBilin (negFourForm c)).Nondegenerate := by
  have h2 : (2 : ZMod 5) ≠ 0 := ZMod.prime_ne_zero 5 2 (by norm_num)
  letI : Invertible (2 : ZMod 5) := invertibleOfNonzero h2
  have hnd : (negFourForm c).Nondegenerate :=
    QuadraticMap.nondegenerate_weightedSumSquares
      (fun _ : Fin 4 => isRegular_iff_ne_zero.mpr hc)
  exact QuadraticMap.nondegenerate_polar_iff.mpr hnd

private lemma negFourForm_isPlusType [Fact (Nat.Prime 5)] (c : ZMod 5) :
    CFSG.GroupTheory.WeirSylow.IsPlusType (negFourForm c) := by
  let u : Fin 4 → ZMod 5 := ![1, 2, 0, 0]
  let v : Fin 4 → ZMod 5 := ![0, 0, 1, 2]
  let L : (Fin 2 → ZMod 5) →ₗ[ZMod 5] (Fin 4 → ZMod 5) :=
    { toFun := fun p => p 0 • u + p 1 • v
      map_add' := by
        intro p q
        simp only [Pi.add_apply, add_smul]
        abel
      map_smul' := by
        intro a p
        simp [Pi.smul_apply, smul_add, smul_smul, smul_eq_mul] }
  have hu0 : negFourForm c u = 0 := by
    rw [negFourForm_apply]
    change c * (1 ^ 2 + 2 ^ 2 + 0 ^ 2 + 0 ^ 2) = 0
    have h5 : (5 : ZMod 5) = 0 := CharP.cast_eq_zero (ZMod 5) 5
    calc c * (1 ^ 2 + 2 ^ 2 + 0 ^ 2 + 0 ^ 2) = c * 5 := by ring
      _ = 0 := by rw [h5, mul_zero]
  have hv0 : negFourForm c v = 0 := by
    rw [negFourForm_apply]
    change c * (0 ^ 2 + 0 ^ 2 + 1 ^ 2 + 2 ^ 2) = 0
    have h5 : (5 : ZMod 5) = 0 := CharP.cast_eq_zero (ZMod 5) 5
    calc c * (0 ^ 2 + 0 ^ 2 + 1 ^ 2 + 2 ^ 2) = c * 5 := by ring
      _ = 0 := by rw [h5, mul_zero]
  have huv : QuadraticMap.polar (negFourForm c) u v = 0 := by
    rw [negFourForm, owPo_polar_weightedSumSquares, Fin.sum_univ_four]
    change 2 * (c * (1 * 0) + c * (2 * 0) + c * (0 * 1) + c * (0 * 2)) = 0
    ring
  have hL_inj : Function.Injective L := by
    intro p q hpq
    have h0 := congrFun hpq (0 : Fin 4)
    have h2 := congrFun hpq (2 : Fin 4)
    have hp0 : p 0 = q 0 := by
      change (p 0 • u + p 1 • v) 0 = (q 0 • u + q 1 • v) 0 at h0
      simpa [u, v, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h0
    have hp1 : p 1 = q 1 := by
      change (p 0 • u + p 1 • v) 2 = (q 0 • u + q 1 • v) 2 at h2
      simpa [u, v, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h2
    funext i
    fin_cases i
    · exact hp0
    · exact hp1
  have hfr : Module.finrank (ZMod 5) (LinearMap.range L) = 2 := by
    rw [LinearMap.finrank_range_of_inj hL_inj, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin]
  have hV : Module.finrank (ZMod 5) (Fin 4 → ZMod 5) = 2 * 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  refine ⟨LinearMap.range L, ?_, ?_⟩
  · rw [hfr, hV]
  · rintro x ⟨p, rfl⟩
    change negFourForm c (p 0 • u + p 1 • v) = 0
    rw [QuadraticMap.map_add (negFourForm c), CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq,
      CFSG.ClassicalGroups.Orthogonal.map_smul_eq_sq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_left_eq,
      CFSG.ClassicalGroups.Orthogonal.polar_smul_right_eq, hu0, hv0, huv]
    ring

theorem neg_mem_closure_classRefl_of_isPlusType_four [Fact (Nat.Prime 5)] {U : Type}
    [AddCommGroup U] [Module (ZMod 5) U] [Module.Finite (ZMod 5) U]
    (hU : Module.finrank (ZMod 5) U = 4)
    {Q : QuadraticForm (ZMod 5) U} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hplus : CFSG.GroupTheory.WeirSylow.IsPlusType Q) {c : ZMod 5} (hc : c ≠ 0) :
    (LinearEquiv.neg (ZMod 5) : U ≃ₗ[ZMod 5] U) ∈ Subgroup.closure (ClassRefl 5 Q c) := by
  have hQ' : (QuadraticMap.polarBilin (negFourForm c)).Nondegenerate :=
    negFourForm_polar_nondegenerate c hc
  have hplus' : CFSG.GroupTheory.WeirSylow.IsPlusType (negFourForm c) :=
    negFourForm_isPlusType c
  have hV' : Module.finrank (ZMod 5) (Fin 4 → ZMod 5) = 2 * 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  obtain ⟨e⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_isPlusType_iff
    (K := ZMod 5) hQ hQ' hU hV' (iff_of_true hplus hplus')
  let f : Fin 4 → U := fun i => e.symm (Pi.single i 1)
  have hfQ : ∀ i, Q (f i) = c := by
    intro i
    rw [show Q (f i) = negFourForm c (Pi.single i 1) by
      simpa [f] using e.symm.map_app (Pi.single i 1)]
    exact negFourForm_apply_single c i
  have hfpol : ∀ i j, i ≠ j → QuadraticMap.polar Q (f i) (f j) = 0 := by
    intro i j hij
    have hpol : ∀ x y : Fin 4 → ZMod 5,
        QuadraticMap.polar Q (e.symm x) (e.symm y) =
          QuadraticMap.polar (negFourForm c) x y := by
      intro x y
      simp only [QuadraticMap.polar, ← map_add, QuadraticMap.IsometryEquiv.map_app]
    rw [hpol]
    exact negFourForm_polar_single c hij
  have hclass : ∀ i, CFSG.ClassicalGroups.Orthogonal.reflect Q (f i) ∈ ClassRefl 5 Q c := by
    intro i
    rw [mem_classRefl_iff (p := 5) (by norm_num) hQ hc]
    exact ⟨f i, hfQ i, rfl⟩
  let r : Fin 4 → U ≃ₗ[ZMod 5] U :=
    fun i => CFSG.ClassicalGroups.Orthogonal.reflect Q (f i)
  let P : U ≃ₗ[ZMod 5] U := r 0 * r 1 * r 2 * r 3
  have hPmem : P ∈ Subgroup.closure (ClassRefl 5 Q c) := by
    dsimp only [P, r]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (hclass 0)) (Subgroup.subset_closure (hclass 1)))
      (Subgroup.subset_closure (hclass 2))) (Subgroup.subset_closure (hclass 3))
  have hfac : ∀ i j, r i (f j) = (if i = j then (-1 : ZMod 5) else 1) • f j := by
    intro i j
    by_cases hij : i = j
    · rw [if_pos hij, ← hij]
      dsimp only [r]
      rw [CFSG.StandardType.ZS.reflect_apply_self (by rw [hfQ i]; exact hc), neg_one_smul]
    · rw [if_neg hij, CFSG.ClassicalGroups.Orthogonal.reflect_apply_of_polar_eq_zero
        (hfpol i j hij), one_smul]
  have hPj : ∀ j, P (f j) = - f j := by
    intro j
    fin_cases j <;>
      simp [P, r, LinearEquiv.mul_apply, hfac, smul_smul, neg_one_smul]
  let b : Module.Basis (Fin 4) (ZMod 5) U :=
    (Pi.basisFun (ZMod 5) (Fin 4)).map e.symm.toLinearEquiv
  have hb : ∀ i, b i = f i := by
    intro i
    simp [b, f, Module.Basis.map_apply, Pi.basisFun_apply]
  have hPlin : (P : U →ₗ[ZMod 5] U) = -(1 : U →ₗ[ZMod 5] U) := by
    refine Module.Basis.ext b fun j => ?_
    rw [hb j]
    simpa [LinearMap.neg_apply] using hPj j
  have hP : P = LinearEquiv.neg (ZMod 5) := by
    refine LinearEquiv.ext fun x => ?_
    have hx := congrArg (fun l : U →ₗ[ZMod 5] U => l x) hPlin
    simpa [LinearEquiv.neg_apply] using hx
  rw [← hP]
  exact hPmem

end CFSG.StandardType.ZS

end
