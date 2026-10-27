module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusSemi
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaFrame
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmModel
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusLevi
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmHyp
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsOmRestr
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthBasic
import CFSG.ClassicalGroups.Orthogonal.Simple
import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

namespace CFSG.StandardType.KGOm

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21
open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.SeitzReduction.OmegaPilot
  RootCentOmega
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup commSpace mem_omegaGroup
  finrank_commSpace_reflection)
open CFSG.StandardType.RCSTOm
open scoped MatrixGroups commutatorElement Pointwise

variable {K : Type} [Field K] {n : ℕ}

theorem quadPlus_vPlusS (hn : 1 ≤ n) : quadPlus n K (vPlusS hn) = 1 := by
  rw [vPlusS, QuadraticMap.map_add (quadPlus n K), quadPlus_plusVec, quadPlus_plusVec,
    polar_quadPlus_plusVec]
  simp

theorem vPlusS_ne_zero (hn : 1 ≤ n) : vPlusS hn ≠ (0 : Fin n ⊕ Fin n → K) := by
  intro h
  have h1 := quadPlus_vPlusS (K := K) hn
  rw [h] at h1
  exact zero_ne_one (show (0 : K) = 1 from by simpa using h1)

theorem polar_vPlusS_plusVec (hn : 1 ≤ n) {m : Fin n} (hm : m ≠ ⟨0, by omega⟩) (r : Bool) :
    polar (quadPlus n K) (vPlusS hn) (plusVec n K m r) = 0 := by
  have h0 : (⟨0, by omega⟩ : Fin n) ≠ m := fun h => hm h.symm
  rw [vPlusS, polar_add_left, polar_quadPlus_plusVec, polar_quadPlus_plusVec]
  simp [h0]

theorem quadPlus_fieldMap (τ : K ≃+* K) (y : Fin n ⊕ Fin n → K) :
    quadPlus n K (fun m => τ (y m)) = τ (quadPlus n K y) := by
  rw [quadPlus_apply, quadPlus_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [map_mul]

theorem polar_fieldMap (τ : K ≃+* K) (y z : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) (fun m => τ (y m)) (fun m => τ (z m)) = τ (polar (quadPlus n K) y z) := by
  rw [polar_quadPlus, polar_quadPlus, map_sum]
  exact Finset.sum_congr rfl fun i _ => by simp only [map_add, map_mul]

theorem fieldMap_vPlusS (hn : 1 ≤ n) (τ : K ≃+* K) :
    (fun m => τ (vPlusS hn m)) = vPlusS hn := by
  funext m
  rcases m with k | k <;> simp [vPlusS, plusVec, Pi.single_apply]

theorem plusSemi_add (hn : 1 ≤ n) (ε : Bool) (τ : K ≃+* K)
    (y z : Fin n ⊕ Fin n → K) :
    plusSemi hn ε τ (y + z) = plusSemi hn ε τ y + plusSemi hn ε τ z := by
  cases ε
  · funext m
    simp only [plusSemi_false, Pi.add_apply, map_add]
  · rw [plusSemi_true, plusSemi_true, plusSemi_true]
    have hL : (fun m => τ ((y + z) m)) = (fun m => τ (y m)) + (fun m => τ (z m)) := by
      funext m
      simp only [Pi.add_apply, map_add]
    rw [hL, polar_add_right, add_smul]
    abel

theorem plusSemi_smul (hn : 1 ≤ n) (ε : Bool) (τ : K ≃+* K) (b : K)
    (y : Fin n ⊕ Fin n → K) :
    plusSemi hn ε τ (b • y) = τ b • plusSemi hn ε τ y := by
  cases ε
  · funext m
    simp only [plusSemi_false, Pi.smul_apply, smul_eq_mul, map_mul]
  · rw [plusSemi_true, plusSemi_true]
    have hL : (fun m => τ ((b • y) m)) = τ b • (fun m => τ (y m)) := by
      funext m
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [hL, polar_smul_right, smul_eq_mul, ← smul_smul, smul_add]

theorem plusSemi_quadratic [CharP K 2] (hn : 1 ≤ n) (ε : Bool) (τ : K ≃+* K)
    (y : Fin n ⊕ Fin n → K) :
    quadPlus n K (plusSemi hn ε τ y) = τ (quadPlus n K y) := by
  cases ε
  · exact quadPlus_fieldMap τ y
  · have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    set c := polar (quadPlus n K) (vPlusS hn) (fun m => τ (y m)) with hc
    have hc' : polar (quadPlus n K) (fun m => τ (y m)) (vPlusS hn) = c := by
      rw [polar_comm, hc]
    have hAy : plusSemi hn true τ y = (fun m => τ (y m)) + c • vPlusS hn := rfl
    rw [hAy, QuadraticMap.map_add (quadPlus n K), QuadraticMap.map_smul, quadPlus_vPlusS,
      quadPlus_fieldMap, polar_smul_right, hc', smul_eq_mul, mul_one, smul_eq_mul]
    have hcc : c * c + c * c = 0 := by
      rw [← two_mul, h2, zero_mul]
    calc τ (quadPlus n K y) + c * c + c * c = τ (quadPlus n K y) + (c * c + c * c) := by
          abel
      _ = τ (quadPlus n K y) + 0 := by rw [hcc]
      _ = τ (quadPlus n K y) := by rw [add_zero]

theorem plusSemi_polar [CharP K 2] (hn : 1 ≤ n) (ε : Bool) (τ : K ≃+* K)
    (y z : Fin n ⊕ Fin n → K) :
    polar (quadPlus n K) (plusSemi hn ε τ y) (plusSemi hn ε τ z) =
      τ (polar (quadPlus n K) y z) := by
  cases ε
  · exact polar_fieldMap τ y z
  · have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    set Ly : Fin n ⊕ Fin n → K := fun m => τ (y m) with hLy
    set Lz : Fin n ⊕ Fin n → K := fun m => τ (z m) with hLz
    set c := polar (quadPlus n K) (vPlusS hn) Ly with hc
    set d := polar (quadPlus n K) (vPlusS hn) Lz with hd
    have hc' : polar (quadPlus n K) Ly (vPlusS hn) = c := by
      rw [polar_comm, hc]
    have hd' : polar (quadPlus n K) Lz (vPlusS hn) = d := by
      rw [polar_comm, hd]
    have hvv : polar (quadPlus n K) (vPlusS hn) (vPlusS hn) = 0 := by
      rw [polar_self_eq_two_mul, h2, zero_mul]
    have hAy : plusSemi hn true τ y = Ly + c • vPlusS hn := rfl
    have hAz : plusSemi hn true τ z = Lz + d • vPlusS hn := rfl
    rw [hAy, hAz, polar_add_left, polar_add_right, polar_add_right, polar_smul_right,
      hc', polar_smul_left, ← hd, polar_smul_left, polar_smul_right, hvv, smul_zero,
      smul_zero, smul_eq_mul, smul_eq_mul]
    rw [polar_fieldMap, add_zero]
    have hcd : d * c + c * d = 0 := by
      rw [mul_comm d c, ← two_mul, h2, zero_mul]
    calc τ (polar (quadPlus n K) y z) + d * c + c * d =
          τ (polar (quadPlus n K) y z) + (d * c + c * d) := by abel
      _ = τ (polar (quadPlus n K) y z) + 0 := by rw [hcd]
      _ = τ (polar (quadPlus n K) y z) := by rw [add_zero]

theorem plusSemi_plusVec (hn : 1 ≤ n) (ε : Bool) (τ : K ≃+* K) {m : Fin n} {r : Bool}
    (hm : m ≠ ⟨0, by omega⟩) :
    plusSemi hn ε τ (plusVec n K m r) = plusVec n K m r := by
  have hB : polar (quadPlus n K) (vPlusS hn) (plusVec n K m r) = 0 :=
    polar_vPlusS_plusVec hn hm r
  have hL : (fun a => τ (plusVec n K m r a)) = plusVec n K m r := by
    funext a
    rcases a with k | k <;> cases r <;> simp [plusVec, Pi.single_apply]
  cases ε
  · rw [plusSemi_false, hL]
  · rw [plusSemi_true, hL, hB, zero_smul, add_zero]

theorem plusSemi_inverse_left [CharP K 2] (hn : 1 ≤ n) (ε : Bool) (τ : K ≃+* K)
    (y : Fin n ⊕ Fin n → K) :
    plusSemi hn ε τ⁻¹ (plusSemi hn ε τ y) = y := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  cases ε
  · funext m
    exact τ.symm_apply_apply (y m)
  · set Ly : Fin n ⊕ Fin n → K := fun m => τ (y m) with hLy
    set c := polar (quadPlus n K) (vPlusS hn) Ly with hc
    have hc_eq : c = τ (polar (quadPlus n K) (vPlusS hn) y) := by
      rw [hc]
      conv_lhs => rw [← fieldMap_vPlusS hn τ]
      exact polar_fieldMap τ (vPlusS hn) y
    have hAy : plusSemi hn true τ y = Ly + c • vPlusS hn := rfl
    have hAf : plusSemi hn true τ⁻¹ (Ly + c • vPlusS hn) =
        (fun m => τ⁻¹ (((Ly + c • vPlusS hn : Fin n ⊕ Fin n → K)) m)) +
          polar (quadPlus n K) (vPlusS hn)
            (fun m => τ⁻¹ (((Ly + c • vPlusS hn : Fin n ⊕ Fin n → K)) m)) • vPlusS hn := rfl
    rw [hAy, hAf]
    have hL : (fun m => τ⁻¹ (((Ly + c • vPlusS hn : Fin n ⊕ Fin n → K)) m)) =
        y + τ⁻¹ c • vPlusS hn := by
      funext m
      have hv : τ⁻¹ (vPlusS hn m) = vPlusS hn m := by
        simpa [congrFun (fieldMap_vPlusS hn τ) m] using τ.symm_apply_apply (vPlusS hn m)
      have hLym : τ⁻¹ (Ly m) = y m := by
        rw [hLy]
        exact τ.symm_apply_apply _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hLym, hv]
    rw [hL]
    have hB : polar (quadPlus n K) (vPlusS hn) (y + τ⁻¹ c • vPlusS hn) = τ⁻¹ c := by
      rw [polar_add_right, polar_smul_right_eq, polar_self_eq_two_mul, h2, zero_mul, mul_zero,
        add_zero, hc_eq]
      exact (τ.symm_apply_apply (polar (quadPlus n K) (vPlusS hn) y)).symm
    rw [hB]
    have hcc : τ⁻¹ c • vPlusS hn + τ⁻¹ c • vPlusS hn =
        (0 : Fin n ⊕ Fin n → K) := by
      rw [← two_smul K (τ⁻¹ c • vPlusS hn), h2, zero_smul]
    rw [show y + τ⁻¹ c • vPlusS hn + τ⁻¹ c • vPlusS hn =
      y + (τ⁻¹ c • vPlusS hn + τ⁻¹ c • vPlusS hn) by abel, hcc, add_zero]

theorem plusSemi_false_eichler (hn : 1 ≤ n) (τ : K ≃+* K)
    {u w y : Fin n ⊕ Fin n → K} (hu : quadPlus n K u = 0)
    (huw : polar (quadPlus n K) u w = 0) :
    plusSemi hn false τ (eichler (quadPlus n K) u w y) =
      eichler (quadPlus n K) (plusSemi hn false τ u) (plusSemi hn false τ w)
        (plusSemi hn false τ y) := by
  have hAu : quadPlus n K (fun m => τ (u m)) = 0 := by
    rw [quadPlus_fieldMap, hu, map_zero]
  have hAuw : polar (quadPlus n K) (fun m => τ (u m)) (fun m => τ (w m)) = 0 := by
    rw [polar_fieldMap, huw, map_zero]
  rw [plusSemi_false, plusSemi_false, plusSemi_false, plusSemi_false]
  funext m
  rw [eichler_apply hu huw, eichler_apply hAu hAuw]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add, map_sub, map_mul,
    polar_fieldMap, quadPlus_fieldMap]

section Reflection

@[instance_reducible] noncomputable def invertible_quadPlus_vPlusS (hn : 1 ≤ n) :
    Invertible (quadPlus n K (vPlusS hn)) :=
  invertibleOfNonzero (by rw [quadPlus_vPlusS]; exact one_ne_zero)

@[expose] noncomputable def plusSemiReflection (hn : 1 ≤ n) :
    (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) :=
  letI : Invertible (quadPlus n K (vPlusS hn)) := invertible_quadPlus_vPlusS hn
  TauCeti.QuadraticMap.reflection (quadPlus n K) (vPlusS hn)

theorem plusSemiReflection_apply [CharP K 2] (hn : 1 ≤ n) (y : Fin n ⊕ Fin n → K) :
    plusSemiReflection hn y = y + polar (quadPlus n K) (vPlusS hn) y • vPlusS hn := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hQ : quadPlus n K (vPlusS hn) = 1 := quadPlus_vPlusS hn
  rw [plusSemiReflection, TauCeti.QuadraticMap.reflection_apply, invOf_eq_inv, hQ, inv_one,
    one_mul, sub_eq_add_neg, neg_eq_self_of_two_eq_zero h2]

theorem plusSemi_true_one_apply [CharP K 2] (hn : 1 ≤ n) (y : Fin n ⊕ Fin n → K) :
    plusSemi hn true 1 y = plusSemiReflection hn y := by
  rw [plusSemi_true, plusSemiReflection_apply]
  simp

theorem plusSemiReflection_mem [CharP K 2] (hn : 1 ≤ n) :
    plusSemiReflection hn ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro y
  rw [← plusSemi_true_one_apply hn y]
  simpa using plusSemi_quadratic hn true 1 y

theorem plusSemiReflection_eq [CharP K 2] (hn : 1 ≤ n) :
    plusSemiReflection hn =
      @TauCeti.QuadraticMap.reflection K (Fin n ⊕ Fin n → K) _ _ _ (quadPlus n K) (vPlusS hn)
        (invertible_quadPlus_vPlusS hn) := by
  refine LinearEquiv.ext fun y => ?_
  rw [plusSemiReflection_apply,
    @TauCeti.QuadraticMap.reflection_apply K (Fin n ⊕ Fin n → K) _ _ _ (quadPlus n K)
      (vPlusS hn) (invertible_quadPlus_vPlusS hn) y]
  rw [invOf_eq_inv, quadPlus_vPlusS, inv_one, one_mul, sub_eq_add_neg,
    neg_eq_self_of_two_eq_zero (CharP.cast_eq_zero K 2)]

theorem plusSemiReflection_plusVec [CharP K 2] (hn : 1 ≤ n) {m : Fin n} {r : Bool}
    (hm : m ≠ ⟨0, by omega⟩) :
    plusSemiReflection hn (plusVec n K m r) = plusVec n K m r := by
  rw [plusSemiReflection_apply, polar_vPlusS_plusVec hn hm r, zero_smul, add_zero]

theorem finrank_commSpace_plusSemiReflection [CharP K 2] (hn : 1 ≤ n) :
    finrank K (commSpace (plusSemiReflection (K := K) hn)) = 1 := by
  rw [plusSemiReflection_eq]
  exact @CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection K _
    (Fin n ⊕ Fin n → K) _ _ _ (quadPlus n K) (nondegenerate_polarBilin_quadPlus n K)
    (vPlusS hn) (invertible_quadPlus_vPlusS hn)

end Reflection

theorem plusSemi_eichler [CharP K 2] (hn : 1 ≤ n) (ε : Bool) (τ : K ≃+* K)
    {u w y : Fin n ⊕ Fin n → K} (hu : quadPlus n K u = 0)
    (huw : polar (quadPlus n K) u w = 0) :
    plusSemi hn ε τ (eichler (quadPlus n K) u w y) =
      eichler (quadPlus n K) (plusSemi hn ε τ u) (plusSemi hn ε τ w)
        (plusSemi hn ε τ y) := by
  cases ε
  · exact plusSemi_false_eichler hn τ hu huw
  · have hA : ∀ z : Fin n ⊕ Fin n → K,
        plusSemi hn true τ z = plusSemiReflection hn (plusSemi hn false τ z) :=
      fun z => plusSemi_true_one_apply (K := K) hn _
    rw [hA, hA, hA, hA, plusSemi_false_eichler hn τ hu huw,
      ← eichler_conj (plusSemiReflection_mem hn) (plusSemi hn false τ u)
        (plusSemi hn false τ w)]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show (plusSemiReflection hn)⁻¹ ((plusSemiReflection hn) (plusSemi hn false τ y)) =
        plusSemi hn false τ y from LinearEquiv.symm_apply_apply _ _]

theorem plusSemi_inverse_right [CharP K 2] (hn : 1 ≤ n) (ε : Bool) (τ : K ≃+* K)
    (y : Fin n ⊕ Fin n → K) :
    plusSemi hn ε τ (plusSemi hn ε τ⁻¹ y) = y := by
  simpa using plusSemi_inverse_left (K := K) (hn := hn) (ε := ε) (τ := τ⁻¹) y

@[expose] noncomputable def plusLevi {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n)
    (i j : Fin n) (s t : Bool) : Subgroup (spinGroup (quadPlus n K)) :=
  (leviFix (elementaryGroup (quadPlus n K)) (framePair (plusFrame n K hn) j t)
      (smulPair (framePair (plusFrame n K hn) i s) one_ne_zero)).comap (spinAction (quadPlus n K)) ⊔
    (omFix (quadPlus n K) (framePair (plusFrame n K hn) j t)
      (smulPair (framePair (plusFrame n K hn) i s) one_ne_zero)).comap (spinAction (quadPlus n K))

theorem c_longRoot_of_plusSemi {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 3 ≤ n) {c : spinGroup (quadPlus n K) →* spinGroup (quadPlus n K)} {ε : Bool}
    {τ : K ≃+* K}
    (hcA : ∀ (k : spinGroup (quadPlus n K)) (y : Fin n ⊕ Fin n → K),
      spinAction (quadPlus n K) (c k) (plusSemi (by omega) ε τ y) =
        plusSemi (by omega) ε τ (spinAction (quadPlus n K) k y))
    {i j : Fin n} (hij : i ≠ j) (hi : i ≠ ⟨0, by omega⟩) (hj : j ≠ ⟨0, by omega⟩)
    (s t : Bool) (b : K) :
    c ((plusFrame n K hn).longRoot hij s t (.ofAdd b)) =
      (plusFrame n K hn).longRoot hij s t (.ofAdd (τ b)) := by
  classical
  have hn1 : 1 ≤ n := by omega
  let F := plusFrame n K hn
  let Q := quadPlus n K
  let u : Fin n ⊕ Fin n → K := plusVec n K j t
  let w : Fin n ⊕ Fin n → K := b • plusVec n K i s
  have hu : Q u = 0 := by
    simpa [Q, u] using quadPlus_plusVec (n := n) (K := K) j t
  have huw : polar Q u w = 0 := by
    rw [polar_smul_right_eq]
    have h1 : polar Q u (plusVec n K i s) = if j = i ∧ t = !s then 1 else 0 := by
      simpa [Q, u] using polar_quadPlus_plusVec (n := n) (K := K) j i t s
    have h0 : polar Q u (plusVec n K i s) = 0 := by
      rw [h1]
      simp [hij.symm]
    rw [h0, mul_zero]
  have hAu : plusSemi hn1 ε τ u = u := by
    simpa [u] using plusSemi_plusVec (K := K) (n := n) (ε := ε) (τ := τ) hn1 (m := j) (r := t) hj
  have hAw : plusSemi hn1 ε τ w = τ b • plusVec n K i s := by
    simp only [w]
    rw [plusSemi_smul,
      plusSemi_plusVec (K := K) (n := n) (ε := ε) (τ := τ) hn1 (m := i) (r := s) hi]
  have hσk : spinAction Q (F.longRoot hij s t (.ofAdd b)) = eichler Q u w := by
    simpa [F, Q, u, w] using RootCentOmega.spinAction_longRoot_eq_eichler F hij s t b
  have hσk' : spinAction Q (F.longRoot hij s t (.ofAdd (τ b))) =
      eichler Q u (τ b • plusVec n K i s) := by
    simpa [F, Q, u] using RootCentOmega.spinAction_longRoot_eq_eichler F hij s t (τ b)
  refine RootCentOmega.spinAction_quadPlus_injective ?_
  refine LinearEquiv.ext fun x => ?_
  set y : Fin n ⊕ Fin n → K := plusSemi hn1 ε τ⁻¹ x with hy
  have hAy : plusSemi hn1 ε τ y = x := plusSemi_inverse_right hn1 ε τ x
  have hcx : spinAction Q (c (F.longRoot hij s t (.ofAdd b))) x =
      plusSemi hn1 ε τ (spinAction Q (F.longRoot hij s t (.ofAdd b)) y) := by
    rw [← hAy]
    simpa using hcA (F.longRoot hij s t (.ofAdd b)) y
  rw [hcx, hσk, plusSemi_eichler hn1 ε τ hu huw, hAu, hAw, hAy, hσk']

theorem eq_self_of_plusLevi_conj {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn5 : 5 ≤ n)
    {c : spinGroup (quadPlus n K) →* spinGroup (quadPlus n K)} {ε : Bool} {τ : K ≃+* K}
    (hcA : ∀ (k : spinGroup (quadPlus n K)) (y : Fin n ⊕ Fin n → K),
      spinAction (quadPlus n K) (c k) (plusSemi (by omega) ε τ y) =
        plusSemi (by omega) ε τ (spinAction (quadPlus n K) k y))
    {i j : Fin n} (hij : i ≠ j) (hi : i ≠ ⟨0, by omega⟩) (hj : j ≠ ⟨0, by omega⟩)
    (s t : Bool) {h : spinGroup (quadPlus n K)} (hh : h ∈ plusLevi (by omega) i j s t)
    (hkey : ∀ k ∈ plusLevi (by omega) i j s t, c k ∈ plusLevi (by omega) i j s t →
      h * c k * h⁻¹ = k) :
    ε = false ∧ τ = 1 ∧ ∀ k, c k = k := by
  have hn3 : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  classical
  let F := plusFrame n K hn3
  let Q := quadPlus n K
  let P₁ : HypPair Q := framePair F j t
  let P₂ : HypPair Q := smulPair (framePair F i s) one_ne_zero
  let L₁ := leviFix (elementaryGroup Q) P₁ P₂
  let L₂ := omFix Q P₁ P₂
  let σ := spinAction Q
  have hQnd : (polarBilin Q).Nondegenerate := by
    simpa [Q] using nondegenerate_polarBilin_quadPlus n K
  have h₁₂ : P₁.Orth P₂ := by
    simpa [P₁, P₂, F] using RCSTOm.orth₁₂ F hij s t one_ne_zero
  have hrange : σ.range = elementaryGroup Q := by
    simpa [σ, Q] using range_spinAction_quadPlus hn3
  have hPL : plusLevi (by omega) i j s t = L₁.comap σ ⊔ L₂.comap σ := rfl
  let k : K → spinGroup Q := fun b => F.longRoot hij (!s) t (.ofAdd b)
  have hσk : ∀ (b : K), σ (k b) = eichler Q P₁.e (b • P₂.f) := by
    intro b
    simpa [k, σ, Q, P₁, P₂, F, framePair, smulPair, inv_one, one_smul]
      using RootCentOmega.spinAction_longRoot_eq_eichler (Q := Q) F hij (!s) t b
  have hk_mem : ∀ (b : K), k b ∈ plusLevi (by omega) i j s t := by
    intro b
    rw [hPL]
    refine Subgroup.mem_sup_left (Subgroup.mem_comap.mpr ?_)
    rw [hσk b]
    exact (eichler_mem_leviFix h₁₂ (eichler_mem_elementaryGroup Q) b).1
  have hk_c : ∀ (b : K), c (k b) = k (τ b) := by
    intro b
    simpa [k, F] using c_longRoot_of_plusSemi hn3 hcA hij hi hj (!s) t b
  have hkey_b : ∀ (b : K), h * k (τ b) * h⁻¹ = k b := by
    intro b
    have h1 := hkey (k b) (hk_mem b) (by rw [hk_c b]; exact hk_mem (τ b))
    rwa [hk_c b] at h1
  have hcomm1 : σ h * σ (k 1) * (σ h)⁻¹ = σ (k 1) := by
    have h1 := hkey_b 1
    rw [show τ 1 = 1 from map_one τ] at h1
    have h2 := congrArg σ h1
    simpa [map_mul, map_inv] using h2
  have hcommE : σ h * eichler Q P₁.e P₂.f = eichler Q P₁.e P₂.f * σ h := by
    have h0 := hcomm1
    rw [hσk 1, one_smul] at h0
    calc σ h * eichler Q P₁.e P₂.f
        = σ h * eichler Q P₁.e P₂.f * (σ h)⁻¹ * σ h := by group
      _ = eichler Q P₁.e P₂.f * σ h := by rw [h0]
  let N : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K) :=
    eichlerLin Q P₁.e P₂.f - LinearMap.id
  have hN_apply : ∀ y, N y = polar Q y P₁.e • P₂.f -
      (polar Q y P₂.f + Q P₂.f * polar Q y P₁.e) • P₁.e := by
    intro y
    simp only [N, LinearMap.sub_apply, eichlerLin_apply, LinearMap.id_apply]
    abel
  have hE_apply : ∀ y, eichler Q P₁.e P₂.f y = y + N y := by
    intro y
    rw [eichler_apply P₁.Q_e h₁₂.ef, hN_apply]
    abel
  have hNcomm : ∀ y, σ h (N y) = N (σ h y) := by
    intro y
    have h1 : σ h (eichler Q P₁.e P₂.f y) = eichler Q P₁.e P₂.f (σ h y) := by
      have h := congrArg (fun e => e y) hcommE
      simpa [LinearEquiv.mul_apply] using h
    rw [hE_apply, hE_apply, map_add] at h1
    exact add_left_cancel h1
  have hEb_apply : ∀ (b : K) (y : Fin n ⊕ Fin n → K),
      eichler Q P₁.e (b • P₂.f) y = y + b • N y := by
    intro b y
    have hQb : Q (b • P₂.f) = 0 := by
      rw [QuadraticMap.map_smul, P₂.Q_f, smul_zero]
    have huwb : polar Q P₁.e (b • P₂.f) = 0 := by
      rw [polar_smul_right_eq, h₁₂.ef, mul_zero]
    rw [eichler_apply P₁.Q_e huwb, hN_apply]
    simp only [polar_smul_right_eq, hQb, P₂.Q_f, mul_zero, zero_mul, add_zero, smul_sub,
      smul_smul]
    module
  have hcommb : ∀ (b : K), σ h * eichler Q P₁.e (b • P₂.f) =
      eichler Q P₁.e (b • P₂.f) * σ h := by
    intro b
    refine LinearEquiv.ext fun x => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hEb_apply, hEb_apply, map_add, map_smul,
      hNcomm]
  have hτb : ∀ (b : K), τ b = b := by
    intro b
    have h1 := congrArg σ (hkey_b b)
    rw [map_mul, map_mul, map_inv, hσk (τ b), hσk b] at h1
    have h2 : eichler Q P₁.e (τ b • P₂.f) = eichler Q P₁.e (b • P₂.f) := by
      have hb' := hcommb b
      calc eichler Q P₁.e (τ b • P₂.f)
          = (σ h)⁻¹ * (σ h * eichler Q P₁.e (τ b • P₂.f) * (σ h)⁻¹) * σ h := by group
        _ = (σ h)⁻¹ * eichler Q P₁.e (b • P₂.f) * σ h := by rw [h1]
        _ = eichler Q P₁.e (b • P₂.f) := by
              calc (σ h)⁻¹ * eichler Q P₁.e (b • P₂.f) * σ h
                  = (σ h)⁻¹ * (eichler Q P₁.e (b • P₂.f) * σ h) := by group
                _ = (σ h)⁻¹ * (σ h * eichler Q P₁.e (b • P₂.f)) := by rw [← hb']
                _ = eichler Q P₁.e (b • P₂.f) := by group
    have hNf : N P₁.f = P₂.f := by
      rw [hN_apply, P₁.polar_fe, h₁₂.ff, P₂.Q_f]
      simp
    have hA := hEb_apply (τ b) P₁.f
    have hB := hEb_apply b P₁.f
    rw [hNf] at hA hB
    have h5 : eichler Q P₁.e (τ b • P₂.f) P₁.f =
        eichler Q P₁.e (b • P₂.f) P₁.f := by rw [h2]
    rw [hA, hB] at h5
    have h4 : τ b • P₂.f = b • P₂.f := add_left_cancel h5
    have hsub : (τ b - b) • P₂.f = 0 := by rw [sub_smul, h4, sub_self]
    rcases smul_eq_zero.mp hsub with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h P₂.f_ne_zero
  have hτ : τ = 1 := RingEquiv.ext hτb
  rw [hτ] at hcA
  have hε : ε = false := by
    cases ε
    · rfl
    · exfalso
      let r := plusSemiReflection (K := K) hn1
      have hcA_r : ∀ kk, σ (c kk) = r * σ kk * r⁻¹ := by
        intro kk
        refine LinearEquiv.ext fun x => ?_
        obtain ⟨y, hy⟩ : ∃ y, r y = x := ⟨r⁻¹ x, LinearEquiv.apply_symm_apply _ _⟩
        rw [← hy]
        have h := hcA kk y
        rw [plusSemi_true_one_apply hn1 y, plusSemi_true_one_apply hn1 (σ kk y)] at h
        rw [h, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          show r⁻¹ (r y) = y from LinearEquiv.symm_apply_apply _ _]
      have hr_e1 : r P₁.e = P₁.e := by
        simpa [r, P₁, F, framePair] using
          plusSemiReflection_plusVec (K := K) (n := n) (m := j) (r := t) hn1 hj
      have hr_f1 : r P₁.f = P₁.f := by
        simpa [r, P₁, F, framePair] using
          plusSemiReflection_plusVec (K := K) (n := n) (m := j) (r := !t) hn1 hj
      have hr_e2 : r P₂.e = P₂.e := by
        simpa [r, P₂, F, smulPair, framePair] using
          plusSemiReflection_plusVec (K := K) (n := n) (m := i) (r := s) hn1 hi
      have hr_f2 : r P₂.f = P₂.f := by
        simpa [r, P₂, F, smulPair, framePair] using
          plusSemiReflection_plusVec (K := K) (n := n) (m := i) (r := !s) hn1 hi
      have hrinv : ∀ x : Fin n ⊕ Fin n → K, r x = x → r⁻¹ x = x := by
        intro x hx
        have h := LinearEquiv.symm_apply_apply r x
        rwa [hx] at h
      have hcL₂ : ∀ kk, kk ∈ L₂.comap σ → c kk ∈ L₂.comap σ := by
        intro kk hk
        rw [Subgroup.mem_comap] at hk ⊢
        obtain ⟨-, hke1, hkf1, hke2, hkf2⟩ := mem_omFix.mp hk
        refine mem_omFix.mpr ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [← hrange]
          exact ⟨c kk, rfl⟩
        · rw [hcA_r kk]
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
            hrinv P₁.e hr_e1, hke1, hr_e1]
        · rw [hcA_r kk]
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
            hrinv P₁.f hr_f1, hkf1, hr_f1]
        · rw [hcA_r kk]
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
            hrinv P₂.e hr_e2, hke2, hr_e2]
        · rw [hcA_r kk]
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
            hrinv P₂.f hr_f2, hkf2, hr_f2]
      have hL₁cent : L₁.comap σ ≤ Subgroup.centralizer (L₂.comap σ : Set (spinGroup Q)) := by
        intro x hx
        have hx' : x ∈ L₁.comap σ := hx
        rw [Subgroup.mem_comap] at hx'
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : y ∈ L₂.comap σ := hy
        rw [Subgroup.mem_comap] at hy'
        have hcomm : σ y * σ x = σ x * σ y :=
          (Subgroup.mem_centralizer_iff.mp (leviFix_le_centralizer_omFix h₁₂ hx')
            (σ y) hy')
        apply RootCentOmega.spinAction_quadPlus_injective
        simpa [σ, map_mul] using hcomm
      have hL₁norm : L₁.comap σ ≤ Subgroup.normalizer (L₂.comap σ : Set (spinGroup Q)) :=
        hL₁cent.trans (Subgroup.centralizer_le_normalizer _)
      have hh' : h ∈ (L₁.comap σ ⊔ L₂.comap σ : Subgroup (spinGroup Q)) := hPL ▸ hh
      have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (L₁.comap σ) (L₂.comap σ)
        hL₁norm
      have hh'' : h ∈ (↑(L₁.comap σ) : Set (spinGroup Q)) *
          (↑(L₂.comap σ) : Set (spinGroup Q)) := by
        rw [← hcoe]
        exact hh'
      rw [Set.mem_mul] at hh''
      obtain ⟨h₁, hh₁, h₂, hh₂, hh_eq⟩ := hh''
      have hh₁' : h₁ ∈ L₁.comap σ := hh₁
      have hh₂' : h₂ ∈ L₂.comap σ := hh₂
      rw [Subgroup.mem_comap] at hh₁' hh₂'
      clear hh₁ hh₂
      let g₂ : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) := σ h₂ * r
      have hσh₂E : σ h₂ ∈ elementaryGroup Q := (mem_omFix.mp hh₂').1
      have hg₂O : g₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        mul_mem (elementaryGroup_le_orthogonalGroup Q hσh₂E) (plusSemiReflection_mem hn1)
      have hg₂_e1 : g₂ P₁.e = P₁.e := by
        dsimp only [g₂]
        rw [LinearEquiv.mul_apply, hr_e1, (mem_omFix.mp hh₂').2.1]
      have hg₂_f1 : g₂ P₁.f = P₁.f := by
        dsimp only [g₂]
        rw [LinearEquiv.mul_apply, hr_f1, (mem_omFix.mp hh₂').2.2.1]
      have hg₂_e2 : g₂ P₂.e = P₂.e := by
        dsimp only [g₂]
        rw [LinearEquiv.mul_apply, hr_e2, (mem_omFix.mp hh₂').2.2.2.1]
      have hg₂_f2 : g₂ P₂.f = P₂.f := by
        dsimp only [g₂]
        rw [LinearEquiv.mul_apply, hr_f2, (mem_omFix.mp hh₂').2.2.2.2]
      have hg₂inv : ∀ x, g₂ x = x → g₂⁻¹ x = x := by
        intro x hx
        have h := LinearEquiv.symm_apply_apply g₂ x
        rwa [hx] at h
      have hcommg : ∀ kk, kk ∈ L₂.comap σ → g₂ * σ kk = σ kk * g₂ := by
        intro kk hk
        have hkL : kk ∈ plusLevi (by omega) i j s t := by
          rw [hPL]; exact Subgroup.mem_sup_right hk
        have hckL : c kk ∈ L₂.comap σ := hcL₂ kk hk
        have hckPL : c kk ∈ plusLevi (by omega) i j s t := by
          rw [hPL]; exact Subgroup.mem_sup_right hckL
        have h1 := hkey kk hkL hckPL
        rw [Subgroup.mem_comap] at hckL
        rw [← hh_eq] at h1
        set X := σ h₂ * σ (c kk) * (σ h₂)⁻¹ with hXdef
        have hXmem : X ∈ L₂ := by
          rw [hXdef]
          exact mul_mem (mul_mem hh₂' hckL) (inv_mem hh₂')
        have hXh₁ : σ h₁ * X = X * σ h₁ :=
          (Subgroup.mem_centralizer_iff.mp (leviFix_le_centralizer_omFix h₁₂ hh₁')
            X hXmem).symm
        have h3 : σ h₁ * X * (σ h₁)⁻¹ = σ kk := by
          have h4 := congrArg σ h1
          have h5 : σ (h₁ * h₂ * c kk * (h₁ * h₂)⁻¹) = σ h₁ * X * (σ h₁)⁻¹ := by
            rw [hXdef]
            simp only [map_mul, map_inv, mul_inv_rev]
            group
          rw [h5] at h4
          exact h4
        have hXeq : X = σ kk := by
          rw [← h3, hXh₁]
          group
        have hck_eq : σ (c kk) = (σ h₂)⁻¹ * σ kk * σ h₂ := by
          calc σ (c kk) = (σ h₂)⁻¹ * X * σ h₂ := by rw [hXdef]; group
            _ = (σ h₂)⁻¹ * σ kk * σ h₂ := by rw [hXeq]
        have h6 : r * σ kk * r⁻¹ = (σ h₂)⁻¹ * σ kk * σ h₂ := by
          rw [← hcA_r kk, hck_eq]
        calc g₂ * σ kk = σ h₂ * r * σ kk := rfl
          _ = σ h₂ * (r * σ kk * r⁻¹) * r := by group
          _ = σ h₂ * ((σ h₂)⁻¹ * σ kk * σ h₂) * r := by rw [h6]
          _ = σ kk * g₂ := by dsimp only [g₂]; group
      have hcomm_omFix : ∀ y ∈ omFix Q P₁ P₂, g₂ * y = y * g₂ := by
        intro y hy
        have hyE : y ∈ elementaryGroup Q := (mem_omFix.mp hy).1
        rw [← hrange] at hyE
        obtain ⟨kk, hk⟩ := hyE
        have hkL₂ : kk ∈ L₂.comap σ := by
          rw [Subgroup.mem_comap, hk]; exact hy
        rw [← hk]
        exact hcommg kk hkL₂
      have hmapW : ∀ x ∈ wSub P₁ P₂, g₂ x ∈ wSub P₁ P₂ := by
        intro x hx
        rw [RCSTOm.mem_wSub] at hx ⊢
        obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
        refine ⟨?_, ?_, ?_, ?_⟩
        · have h1 : polar Q P₁.e (g₂ x) = polar Q (g₂⁻¹ P₁.e) x := by
            conv_lhs => rw [← LinearEquiv.apply_symm_apply g₂ P₁.e]
            exact polar_map_of_mem hg₂O _ _
          rw [h1, hg₂inv P₁.e hg₂_e1, hx1]
        · have h1 : polar Q P₁.f (g₂ x) = polar Q (g₂⁻¹ P₁.f) x := by
            conv_lhs => rw [← LinearEquiv.apply_symm_apply g₂ P₁.f]
            exact polar_map_of_mem hg₂O _ _
          rw [h1, hg₂inv P₁.f hg₂_f1, hx2]
        · have h1 : polar Q P₂.e (g₂ x) = polar Q (g₂⁻¹ P₂.e) x := by
            conv_lhs => rw [← LinearEquiv.apply_symm_apply g₂ P₂.e]
            exact polar_map_of_mem hg₂O _ _
          rw [h1, hg₂inv P₂.e hg₂_e2, hx3]
        · have h1 : polar Q P₂.f (g₂ x) = polar Q (g₂⁻¹ P₂.f) x := by
            conv_lhs => rw [← LinearEquiv.apply_symm_apply g₂ P₂.f]
            exact polar_map_of_mem hg₂O _ _
          rw [h1, hg₂inv P₂.f hg₂_f2, hx4]
      have hg₂invO : g₂⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q := inv_mem hg₂O
      have hmapWinv : ∀ x ∈ wSub P₁ P₂, g₂⁻¹ x ∈ wSub P₁ P₂ := by
        intro x hx
        rw [RCSTOm.mem_wSub] at hx ⊢
        obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
        refine ⟨?_, ?_, ?_, ?_⟩
        · have h1 : polar Q P₁.e (g₂⁻¹ x) = polar Q P₁.e x := by
            have h := polar_map_of_mem hg₂O (g₂⁻¹ P₁.e) (g₂⁻¹ x)
            rw [show g₂ (g₂⁻¹ P₁.e) = P₁.e from LinearEquiv.apply_symm_apply g₂ P₁.e,
              show g₂ (g₂⁻¹ x) = x from LinearEquiv.apply_symm_apply g₂ x,
              hg₂inv P₁.e hg₂_e1] at h
            exact h.symm
          rw [h1, hx1]
        · have h1 : polar Q P₁.f (g₂⁻¹ x) = polar Q P₁.f x := by
            have h := polar_map_of_mem hg₂O (g₂⁻¹ P₁.f) (g₂⁻¹ x)
            rw [show g₂ (g₂⁻¹ P₁.f) = P₁.f from LinearEquiv.apply_symm_apply g₂ P₁.f,
              show g₂ (g₂⁻¹ x) = x from LinearEquiv.apply_symm_apply g₂ x,
              hg₂inv P₁.f hg₂_f1] at h
            exact h.symm
          rw [h1, hx2]
        · have h1 : polar Q P₂.e (g₂⁻¹ x) = polar Q P₂.e x := by
            have h := polar_map_of_mem hg₂O (g₂⁻¹ P₂.e) (g₂⁻¹ x)
            rw [show g₂ (g₂⁻¹ P₂.e) = P₂.e from LinearEquiv.apply_symm_apply g₂ P₂.e,
              show g₂ (g₂⁻¹ x) = x from LinearEquiv.apply_symm_apply g₂ x,
              hg₂inv P₂.e hg₂_e2] at h
            exact h.symm
          rw [h1, hx3]
        · have h1 : polar Q P₂.f (g₂⁻¹ x) = polar Q P₂.f x := by
            have h := polar_map_of_mem hg₂O (g₂⁻¹ P₂.f) (g₂⁻¹ x)
            rw [show g₂ (g₂⁻¹ P₂.f) = P₂.f from LinearEquiv.apply_symm_apply g₂ P₂.f,
              show g₂ (g₂⁻¹ x) = x from LinearEquiv.apply_symm_apply g₂ x,
              hg₂inv P₂.f hg₂_f2] at h
            exact h.symm
          rw [h1, hx4]
      let z : wSub P₁ P₂ ≃ₗ[K] wSub P₁ P₂ :=
        CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv (wSub P₁ P₂) g₂ hmapW hmapWinv
      have hfix_uPart : ∀ v, g₂ (uPart P₁ P₂ v) = uPart P₁ P₂ v := by
        intro v
        simp only [uPart, map_add, map_smul, hg₂_e1, hg₂_f1, hg₂_e2, hg₂_f2]
      have hextW : extW P₁ P₂ h₁₂ z = g₂ := by
        refine LinearEquiv.ext fun v => ?_
        rw [extW_apply]
        have hz : (z ⟨v - uPart P₁ P₂ v, mem_wSub.mpr (inW_sub_uPart h₁₂ v)⟩ :
            Fin n ⊕ Fin n → K) = g₂ (v - uPart P₁ P₂ v) :=
          CFSG.RankThree.PartOne.KCOrthogonal.coe_restrictEquiv (wSub P₁ P₂) g₂ hmapW
            hmapWinv ⟨v - uPart P₁ P₂ v, mem_wSub.mpr (inW_sub_uPart h₁₂ v)⟩
        rw [hz, map_sub, hfix_uPart]
        abel
      have hextW_inj : Function.Injective (extW P₁ P₂ h₁₂) := by
        intro a b hab
        refine LinearEquiv.ext fun w => ?_
        have h := congrArg (fun e : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) =>
          e (w : Fin n ⊕ Fin n → K)) hab
        simp only [extW_apply_w] at h
        exact Subtype.ext h
      have hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub P₁ P₂)) := by
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
        intro w
        rw [QuadraticMap.restrict_apply, QuadraticMap.restrict_apply]
        change Q (g₂ (w : Fin n ⊕ Fin n → K)) = Q (w : Fin n ⊕ Fin n → K)
        exact map_of_mem hg₂O (w : Fin n ⊕ Fin n → K)
      have hzc : ∀ y ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub P₁ P₂)),
          TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (wSub P₁ P₂))⁆,
          z * y = y * z := by
        intro y hy
        have hOE : orthDerived Q ≤ elementaryGroup Q := by
          rw [orthDerived, commutator_orthogonalGroup_quadPlus hn3]
        have hyE : extW P₁ P₂ h₁₂ y ∈ elementaryGroup Q :=
          hOE (extW_mem_orthDerived h₁₂ hy)
        have hyom : extW P₁ P₂ h₁₂ y ∈ omFix Q P₁ P₂ := by
          refine mem_omFix.mpr ⟨hyE, ?_, ?_, ?_, ?_⟩
          · exact extW_apply_u h₁₂ y mem_spanU₄_e₁
          · exact extW_apply_u h₁₂ y mem_spanU₄_f₁
          · exact extW_apply_u h₁₂ y mem_spanU₄_e₂
          · exact extW_apply_u h₁₂ y mem_spanU₄_f₂
        have hcomm := hcomm_omFix _ hyom
        apply hextW_inj
        rw [map_mul, map_mul, hextW]
        exact hcomm
      have hdimW : 6 ≤ finrank K (wSub P₁ P₂) := by
        have h := RCSTOm.finrank_wSub_add_four (Q := Q) h₁₂
        have hV : finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
          ring
        omega
      have hz1 : z = 1 := by
        refine LayerCores.OrthRegular.eq_one_of_commute_orthDerived
          (RCSTOm.nondegenerate_restrict_wSub hQnd h₁₂) (by omega) ?_ hzO hzc
        rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> omega
      have hg₂1 : g₂ = 1 := by rw [← hextW, hz1, map_one]
      have hr_eq : r = (σ h₂)⁻¹ := by
        calc r = (σ h₂)⁻¹ * (σ h₂ * r) := by group
          _ = (σ h₂)⁻¹ * 1 := by rw [show σ h₂ * r = 1 from hg₂1]
          _ = (σ h₂)⁻¹ := by rw [mul_one]
      have hrE : r ∈ elementaryGroup Q := by
        rw [hr_eq]
        exact inv_mem hσh₂E
      have hrΩ : r ∈ omegaGroup Q hQnd :=
        RootCentOmega.elementaryGroup_quadPlus_le_omegaGroup hn3 hrE
      have heven : Even (finrank K (commSpace r)) := (mem_omegaGroup.mp hrΩ).2
      rw [finrank_commSpace_plusSemiReflection hn1] at heven
      rcases heven with ⟨kk, hk⟩
      omega
  refine ⟨hε, hτ, ?_⟩
  intro kk
  apply RootCentOmega.spinAction_quadPlus_injective
  refine LinearEquiv.ext fun y => ?_
  have h := hcA kk y
  rw [hε] at h
  simpa [plusSemi_false_one] using h

end CFSG.StandardType.KGOm

end
