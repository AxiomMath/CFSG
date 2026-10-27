module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusFix

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.Spin CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL
  CFSG.ComponentClassification.OuterAutomorphisms QuadraticMap

namespace AutOm

section Eichler

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

@[expose] noncomputable def eichlerC (u w y : Fin d → K) : Fin d → K :=
  y + polar Q y u • w - polar Q y w • u - (Q w * polar Q y u) • u

theorem semilinear_eichlerC (g : coordinateSemilinearGroup d K)
    (hg : ∀ y, Q (coordinateSemilinearMap g y) = g.right (Q y)) (u w y : Fin d → K) :
    coordinateSemilinearMap g (eichlerC Q u w y) =
      eichlerC Q (coordinateSemilinearMap g u) (coordinateSemilinearMap g w)
        (coordinateSemilinearMap g y) := by
  have hp : ∀ a b, polar Q (coordinateSemilinearMap g a) (coordinateSemilinearMap g b) =
      g.right (polar Q a b) := by
    intro a b
    simp only [polar, ← map_add, hg, map_sub]
  simp only [eichlerC, map_sub, map_add, coordinateSemilinearMap_smul, hp, hg, map_mul]

theorem conjAct_fix_of_eichler (g : similarityPairs Q)
    (hg : ∀ y, Q (coordinateSemilinearMap g.val y) = g.val.right (Q y)) (X : matrixDerived Q)
    {u w : Fin d → K}
    (hX : ∀ y, Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y = eichlerC Q u w y)
    (hu : coordinateSemilinearMap g.val u = u) (hw : coordinateSemilinearMap g.val w = w) :
    conjAct Q g X = X := by
  rw [conjAct_apply_eq_self_iff]
  intro y
  rw [hX, hX, semilinear_eichlerC Q g.val hg, hu, hw]

end Eichler

section Plus

open CFSG.SeitzReduction
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldPair fieldPair_val)

variable {K : Type} [Field K] {n : ℕ}

theorem form_pvec (k : Fin n) (r : Bool) : coordinateQuadPlus n K (pvec k r) = 0 := by
  change reindexQuadraticForm _ _ _ = 0
  rw [reindexQuadraticForm_map, quadPlus_plusVec]

theorem spinModelPlus_longRoot_eichler (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (c : K) (y : Fin (2 * n) → K) :
    Matrix.mulVec ((spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd c)) :
        GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) y =
      eichlerC (coordinateQuadPlus n K) (pvec j t) (c • pvec i s) y := by
  rw [spinModelPlus_longRoot_mulVec, eichlerC, QuadraticMap.map_smul, form_pvec, smul_zero,
    zero_mul, zero_smul, sub_zero, polar_smul_right, smul_smul, smul_eq_mul,
    mul_comm (polar (coordinateQuadPlus n K) y (pvec j t)) c]

theorem coordinateSemilinearMap_fieldPair (σ : K ≃+* K) (y : Fin (2 * n) → K) :
    coordinateSemilinearMap (fieldPair (coordinateQuadPlus n K) σ
      (E7Pilot.coordinateQuadPlus_fieldMap n σ)).val y = coordinateFieldMap (2 * n) σ y := by
  funext k
  simp [coordinateSemilinearMap_apply, coordinateFieldMap_apply, fieldPair_val]

theorem coordinateFieldMap_pvec (σ : K ≃+* K) (k : Fin n) (r : Bool) :
    coordinateFieldMap (2 * n) σ (pvec k r) = pvec k r := by
  funext a
  rw [coordinateFieldMap_apply]
  cases r
  · rw [pvec_false, Pi.single_apply]
    split_ifs <;> simp
  · rw [pvec_true, Pi.single_apply]
    split_ifs <;> simp

end Plus

section Pairs

open CFSG.SeitzReduction
open CFSG.RankThree.PartOne.KCOrthogonalSubfield (fieldPair fieldPair_val)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

noncomputable abbrev vPlus (hn : 1 ≤ n) : Fin (2 * n) → K := OmegaPilot.plusUnitVector hn

theorem reflMat_vPlus_mulVec (hn : 1 ≤ n) (y : Fin (2 * n) → K) :
    Matrix.mulVec ((reflMat (coordinateQuadPlus n K) (vPlus hn) (plusUnitVector_form_ne_zero hn) :
      GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) y =
        y + polar (coordinateQuadPlus n K) (vPlus hn) y • vPlus hn :=
  reflMat_mulVec_one _ (plusUnitVector_form hn) _ y

theorem polar_vPlus_pvec (hn : 1 ≤ n) {k : Fin n} (hk : k ≠ ⟨0, by omega⟩) (r : Bool) :
    polar (coordinateQuadPlus n K) (vPlus hn) (pvec k r) = 0 := by
  rw [vPlus, plusUnitVector_eq, polar_add_left, polar_pvec_of_ne (Ne.symm hk),
    polar_pvec_of_ne (Ne.symm hk), add_zero]

theorem reflMat_vPlus_pvec (hn : 1 ≤ n) {k : Fin n} (hk : k ≠ ⟨0, by omega⟩) (r : Bool) :
    Matrix.mulVec ((reflMat (coordinateQuadPlus n K) (vPlus hn) (plusUnitVector_form_ne_zero hn) :
      GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) (pvec k r) = pvec k r := by
  rw [reflMat_vPlus_mulVec, polar_vPlus_pvec hn hk, zero_smul, add_zero]

theorem reflMat_vPlus_pvec_zero (hn : 1 ≤ n) (r : Bool) :
    Matrix.mulVec ((reflMat (coordinateQuadPlus n K) (vPlus hn) (plusUnitVector_form_ne_zero hn) :
      GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) (pvec ⟨0, by omega⟩ r) =
        pvec ⟨0, by omega⟩ (!r) := by
  have h2 : ∀ x : Fin (2 * n) → K, x + x = 0 := fun x => by
    funext a
    exact CharTwo.add_self_eq_zero (x a)
  have e1 : polar (coordinateQuadPlus n K) (pvec (⟨0, by omega⟩ : Fin n) true)
      (pvec ⟨0, by omega⟩ false) = 1 := polar_pvec_not _ true
  have e2 : polar (coordinateQuadPlus n K) (pvec (⟨0, by omega⟩ : Fin n) false)
      (pvec ⟨0, by omega⟩ true) = 1 := polar_pvec_not _ false
  rw [reflMat_vPlus_mulVec, vPlus, plusUnitVector_eq, polar_add_left]
  cases r
  · rw [e1, polar_pvec_self, add_zero, one_smul, add_comm (pvec _ true), ← add_assoc, h2,
      zero_add]
    rfl
  · rw [e2, polar_pvec_self, zero_add, one_smul, ← add_assoc, h2, zero_add]
    rfl

noncomputable abbrev gRefl (hn : 1 ≤ n) : similarityPairs (coordinateQuadPlus n K) :=
  matrixIsometryInclusion _ ⟨reflMat (coordinateQuadPlus n K) (vPlus hn)
    (plusUnitVector_form_ne_zero hn), reflMat_mem_isometries _ _⟩

noncomputable abbrev gField (σ : K ≃+* K) : similarityPairs (coordinateQuadPlus n K) :=
  fieldPair (coordinateQuadPlus n K) σ (E7Pilot.coordinateQuadPlus_fieldMap n σ)

theorem plusRefl_eq (hn : 1 ≤ n) : plusRefl (K := K) hn = conjAct _ (gRefl hn) := rfl

omit [Finite K] [CharP K 2] in
theorem fieldAutP_eq (σ : K ≃+* K) : fieldAutP n σ = conjAct _ (gField (n := n) σ) := rfl

theorem plusRefl_mul_fieldAutP_eq (hn : 1 ≤ n) (σ : K ≃+* K) :
    plusRefl hn * fieldAutP n σ = conjAct _ (gRefl hn * gField σ) := by
  rw [plusRefl_eq, fieldAutP_eq, map_mul]

theorem gRefl_form (hn : 1 ≤ n) (y : Fin (2 * n) → K) :
    coordinateQuadPlus n K (coordinateSemilinearMap (gRefl (K := K) hn).val y) =
      (gRefl (K := K) hn).val.right (coordinateQuadPlus n K y) := by
  rw [coordinateSemilinearMap_inclusion, map_mulVec_of_mem (reflMat_mem_isometries _ _)]
  rfl

omit [Finite K] [CharP K 2] in
theorem gField_form (σ : K ≃+* K) (y : Fin (2 * n) → K) :
    coordinateQuadPlus n K (coordinateSemilinearMap (gField (n := n) σ).val y) =
      (gField (n := n) σ).val.right (coordinateQuadPlus n K y) := by
  rw [coordinateSemilinearMap_fieldPair, E7Pilot.coordinateQuadPlus_fieldMap]
  rfl

theorem gReflField_map (hn : 1 ≤ n) (σ : K ≃+* K) (y : Fin (2 * n) → K) :
    coordinateSemilinearMap (gRefl hn * gField (n := n) σ).val y =
      Matrix.mulVec ((reflMat (coordinateQuadPlus n K) (vPlus hn) (plusUnitVector_form_ne_zero hn) :
        GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)
          (coordinateFieldMap (2 * n) σ y) := by
  change coordinateSemilinearMap ((gRefl hn).val * (gField σ).val) y = _
  rw [coordinateSemilinearMap_mul, coordinateSemilinearMap_fieldPair,
    coordinateSemilinearMap_inclusion]

theorem gReflField_form (hn : 1 ≤ n) (σ : K ≃+* K) (y : Fin (2 * n) → K) :
    coordinateQuadPlus n K (coordinateSemilinearMap (gRefl hn * gField (n := n) σ).val y) =
      (gRefl hn * gField (n := n) σ).val.right (coordinateQuadPlus n K y) := by
  rw [gReflField_map, map_mulVec_of_mem (reflMat_mem_isometries _ _),
    E7Pilot.coordinateQuadPlus_fieldMap]
  change _ = (1 * σ) _
  rw [one_mul]

end Pairs

section FixedSpace

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem conjAct_apply_eq_of (g : similarityPairs Q) (X Y : matrixDerived Q)
    (h : ∀ y, coordinateSemilinearMap g.val
        (Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y) =
      Matrix.mulVec ((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (coordinateSemilinearMap g.val y)) : conjAct Q g X = Y := by
  apply Subtype.ext
  apply Units.ext
  refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  change Matrix.mulVec (((conjAct Q g X : matrixDerived Q) : GL (Fin d) K) :
    Matrix (Fin d) (Fin d) K) v = _
  rw [show Matrix.mulVec (((conjAct Q g X : matrixDerived Q) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) v = coordinateSemilinearMap g.val
        (Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
          ((coordinateSemilinearMap g.val).symm v)) from matrixConjugation_vector g.val X.val v,
    h, AddEquiv.apply_symm_apply]

theorem conjAct_eichler_eq (g : similarityPairs Q)
    (hg : ∀ y, Q (coordinateSemilinearMap g.val y) = g.val.right (Q y)) (X Y : matrixDerived Q)
    {u w w' : Fin d → K}
    (hX : ∀ y, Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y = eichlerC Q u w y)
    (hY : ∀ y, Matrix.mulVec ((Y : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y = eichlerC Q u w' y)
    (hu : coordinateSemilinearMap g.val u = u) (hw : coordinateSemilinearMap g.val w = w') :
    conjAct Q g X = Y :=
  conjAct_apply_eq_of g X Y fun y => by rw [hX, hY, semilinear_eichlerC Q g.val hg, hu, hw]

theorem mulVec_mul (A B : matrixDerived Q) (y : Fin d → K) :
    Matrix.mulVec (((A * B : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y =
      Matrix.mulVec ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (Matrix.mulVec ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y) := by
  rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec]

@[expose] def fixSpace (S : Subgroup (matrixDerived Q)) : Submodule K (Fin d → K) where
  carrier := {y | ∀ q ∈ S,
    Matrix.mulVec (((q : matrixDerived Q) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y = y}
  add_mem' := by
    intro a b ha hb q hq
    rw [Matrix.mulVec_add, ha q hq, hb q hq]
  zero_mem' := fun q _ => Matrix.mulVec_zero _
  smul_mem' := by
    intro c a ha q hq
    rw [Matrix.mulVec_smul, ha q hq]

theorem mulVec_mem_fixSpace {c : MulAut (matrixDerived Q)} {S : Subgroup (matrixDerived Q)}
    (hnorm : ∀ y, c y = y → ∀ q ∈ S, y * q * y⁻¹ ∈ S) {X : matrixDerived Q} (hX : c X = X)
    {y : Fin d → K} (hy : y ∈ fixSpace S) :
    Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y ∈ fixSpace S := by
  intro q hq
  have h := hy _ (hnorm X⁻¹ (by rw [map_inv, hX]) q hq)
  rw [inv_inv, mulVec_mul, mulVec_mul] at h
  have h' := congrArg (Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) h
  rwa [← mulVec_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one, Matrix.one_mulVec] at h'

end FixedSpace

section Fix

open CFSG.SeitzReduction

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem fieldAutP_fix_longRoot (hn : 3 ≤ n) (σ : K ≃+* K) {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) :
    fieldAutP n σ (spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd 1))) =
      spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd 1)) := by
  rw [fieldAutP_eq]
  refine conjAct_fix_of_eichler _ (gField σ) (gField_form σ) _
    (spinModelPlus_longRoot_eichler hn hij s t 1) ?_ ?_
  · rw [coordinateSemilinearMap_fieldPair, coordinateFieldMap_pvec]
  · rw [one_smul, coordinateSemilinearMap_fieldPair, coordinateFieldMap_pvec]

theorem plusRefl_fix_longRoot (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j)
    (hi : i ≠ ⟨0, by omega⟩) (hj : j ≠ ⟨0, by omega⟩) (s t : Bool) (c : K) :
    plusRefl (by omega) (spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd c))) =
      spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd c)) := by
  rw [plusRefl_eq]
  refine conjAct_fix_of_eichler _ (gRefl _) (gRefl_form _) _
    (spinModelPlus_longRoot_eichler hn hij s t c) ?_ ?_
  · rw [coordinateSemilinearMap_inclusion, reflMat_vPlus_pvec _ hj]
  · rw [coordinateSemilinearMap_inclusion, Matrix.mulVec_smul, reflMat_vPlus_pvec _ hi]

theorem reflField_fix_longRoot (hn : 3 ≤ n) (σ : K ≃+* K) {i j : Fin n} (hij : i ≠ j)
    (hi : i ≠ ⟨0, by omega⟩) (hj : j ≠ ⟨0, by omega⟩) (s t : Bool) :
    (plusRefl (K := K) (by omega : 1 ≤ n) * fieldAutP n σ :
        MulAut (matrixDerived (coordinateQuadPlus n K)))
        (spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd 1))) =
      spinModelPlus hn ((plusFrame n K hn).longRoot hij s t (.ofAdd 1)) := by
  rw [plusRefl_mul_fieldAutP_eq]
  refine conjAct_fix_of_eichler _ _ (gReflField_form _ σ) _
    (spinModelPlus_longRoot_eichler hn hij s t 1) ?_ ?_
  · rw [gReflField_map, coordinateFieldMap_pvec, reflMat_vPlus_pvec _ hj]
  · rw [one_smul, gReflField_map, coordinateFieldMap_pvec, reflMat_vPlus_pvec _ hi]

end Fix

section ReflOTwo

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Finite K] in
theorem reflAut_apply_eq_iff (hnd : Q.polarBilin.Nondegenerate) {w : Fin d → K} (hw : Q w = 1)
    (hw0 : Q w ≠ 0) (X : matrixDerived Q) :
    reflAut Q w hw0 X = X ↔
      Matrix.mulVec ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) w = w := by
  have hXO : (X : GL (Fin d) K) ∈ matrixIsometries Q := matrixDerived_le_isometries _ X.2
  rw [← comm_reflMat_iff hnd hXO hw hw0]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [reflAut_apply_val] at h'
    calc (X : GL (Fin d) K) * reflMat Q w hw0 =
        reflMat Q w hw0 * X * (reflMat Q w hw0)⁻¹ * reflMat Q w hw0 := by rw [h']
      _ = _ := by rw [inv_mul_cancel_right]
  · intro h
    apply Subtype.ext
    rw [reflAut_apply_val, ← h, mul_inv_cancel_right]

theorem eq_bot_of_reflAut (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {w : Fin d → K} (hw : Q w = 1) (hw0 : Q w ≠ 0) (hd : 3 ≤ d) (S : Subgroup (matrixDerived Q))
    (hfix : ∀ q ∈ S, reflAut Q w hw0 q = q) (hS : IsPGroup 2 S)
    (hnorm : ∀ y, reflAut Q w hw0 y = y → ∀ q ∈ S, y * q * y⁻¹ ∈ S) : S = ⊥ := by
  set R := S.map (matrixDerived Q).subtype with hRdef
  have hR : R = ⊥ := by
    refine eq_bot_of_normal_two_subgroup hnd hT hw hd R (hS.map _) ?_ ?_ ?_
    · rintro _ ⟨q, -, rfl⟩
      exact q.2
    · rintro _ ⟨q, hq, rfl⟩
      exact (reflAut_apply_eq_iff hnd hw hw0 q).1 (hfix q hq)
    · rintro s hs hsw _ ⟨q, hq, rfl⟩
      have hy := (reflAut_apply_eq_iff hnd hw hw0 ⟨s, hs⟩).2 hsw
      exact ⟨_, hnorm _ hy q hq, rfl⟩
  rw [hRdef] at hR
  exact (Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective).1 hR

end ReflOTwo

section PlusOTwo

open CFSG.SeitzReduction

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem eq_bot_of_plusRefl (hn : 3 ≤ n) (S : Subgroup (matrixDerived (coordinateQuadPlus n K)))
    (hfix : ∀ q ∈ S, plusRefl (by omega) q = q) (hS : IsPGroup 2 S)
    (hnorm : ∀ y, plusRefl (by omega) y = y → ∀ q ∈ S, y * q * y⁻¹ ∈ S) : S = ⊥ := by
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus n K hn
  exact eq_bot_of_reflAut hnd hT (plusUnitVector_form (by omega)) _ (by omega) S hfix hS hnorm

omit [Finite K] [CharP K 2] in
theorem exists_polar_pvec_ne_zero {y : Fin (2 * n) → K} (hy : y ≠ 0) :
    ∃ k r, polar (coordinateQuadPlus n K) y (pvec k r) ≠ 0 := by
  by_contra h
  push Not at h
  exact hy (eq_zero_of_polar_pvec h)

theorem eq_bot_of_fieldAutP (hn : 3 ≤ n) (σ : K ≃+* K)
    (S : Subgroup (matrixDerived (coordinateQuadPlus n K)))
    (hS : IsPGroup 2 S) (hnorm : ∀ y, fieldAutP n σ y = y → ∀ q ∈ S, y * q * y⁻¹ ∈ S) :
    S = ⊥ := by
  obtain ⟨x, hx0, hx⟩ := exists_fixed_ne_zero (by omega) S hS
  have hW : ∀ i j : Fin n, i ≠ j → ∀ s t : Bool, True → True →
      ∀ y ∈ fixSpace S, eich i j s t y ∈ fixSpace S := by
    intro i j hij s t _ _ y hy
    have h := mulVec_mem_fixSpace hnorm (fieldAutP_fix_longRoot hn σ hij s t) hy
    rwa [spinModelPlus_longRoot_mulVec, one_mul, one_mul] at h
  obtain ⟨k, r, hkr⟩ := exists_polar_pvec_ne_zero hx0
  have hall := spread (fixSpace S) (fun _ => True) hW
    (fun a b => (exists_ne_and_ne hn a b).imp fun c hc => ⟨trivial, hc⟩) hx trivial hkr
  have htop := eq_top_of_pvec_mem fun k r => hall k r trivial
  refine eq_bot_of_fix_top S fun q hq y => ?_
  have hy : y ∈ fixSpace S := htop ▸ Submodule.mem_top
  exact hy q hq

end PlusOTwo

section GraphField

open CFSG.SeitzReduction

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem zero_ne_one_idx (hn : 3 ≤ n) : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
  simp [Fin.ext_iff]

noncomputable abbrev ySpin (hn : 3 ≤ n) (σ : K ≃+* K) (a : K) : spinGroup (quadPlus n K) :=
  (plusFrame n K hn).longRoot (zero_ne_one_idx hn) true true (.ofAdd a) *
    (plusFrame n K hn).longRoot (zero_ne_one_idx hn) false true (.ofAdd (σ a))

theorem reflField_fix_ySpin (hn : 3 ≤ n) {σ : K ≃+* K} (hσσ : σ * σ = 1) (a : K) :
    (plusRefl (K := K) (by omega : 1 ≤ n) * fieldAutP n σ :
        MulAut (matrixDerived (coordinateQuadPlus n K))) (spinModelPlus hn (ySpin hn σ a)) =
      spinModelPlus hn (ySpin hn σ a) := by
  have hσa : σ (σ a) = a := by
    have := congrArg (fun τ : K ≃+* K => τ a) hσσ
    exact this
  have hu : coordinateSemilinearMap (gRefl (K := K) (by omega : 1 ≤ n) * gField (n := n) σ).val
      (pvec ⟨1, by omega⟩ true) = pvec ⟨1, by omega⟩ true := by
    rw [gReflField_map, coordinateFieldMap_pvec,
      reflMat_vPlus_pvec _ (zero_ne_one_idx hn).symm]
  have h1 : (plusRefl (K := K) (by omega : 1 ≤ n) * fieldAutP n σ :
      MulAut (matrixDerived (coordinateQuadPlus n K)))
        (spinModelPlus hn ((plusFrame n K hn).longRoot (zero_ne_one_idx hn) true true
          (.ofAdd a))) =
      spinModelPlus hn ((plusFrame n K hn).longRoot (zero_ne_one_idx hn) false true
        (.ofAdd (σ a))) := by
    rw [plusRefl_mul_fieldAutP_eq]
    refine conjAct_eichler_eq _ (gReflField_form _ σ) _ _
      (spinModelPlus_longRoot_eichler hn _ true true a)
      (spinModelPlus_longRoot_eichler hn _ false true (σ a)) hu ?_
    rw [gReflField_map, coordinateFieldMap_smul, coordinateFieldMap_pvec, Matrix.mulVec_smul,
      reflMat_vPlus_pvec_zero]
    rfl
  have h2 : (plusRefl (K := K) (by omega : 1 ≤ n) * fieldAutP n σ :
      MulAut (matrixDerived (coordinateQuadPlus n K)))
        (spinModelPlus hn ((plusFrame n K hn).longRoot (zero_ne_one_idx hn) false true
          (.ofAdd (σ a)))) =
      spinModelPlus hn ((plusFrame n K hn).longRoot (zero_ne_one_idx hn) true true
        (.ofAdd a)) := by
    rw [plusRefl_mul_fieldAutP_eq]
    refine conjAct_eichler_eq _ (gReflField_form _ σ) _ _
      (spinModelPlus_longRoot_eichler hn _ false true (σ a))
      (spinModelPlus_longRoot_eichler hn _ true true a) hu ?_
    rw [gReflField_map, coordinateFieldMap_smul, coordinateFieldMap_pvec, Matrix.mulVec_smul,
      reflMat_vPlus_pvec_zero, hσa]
    rfl
  rw [ySpin, map_mul, map_mul, h1, h2, ← map_mul, ← map_mul,
    ((plusFrame n K hn).commute_longRoot_longRoot_right (zero_ne_one_idx hn)
      (zero_ne_one_idx hn) true true false a (σ a)).eq]

omit [Finite K] [CharP K 2] in
theorem ySpin_mulVec_of_polar (hn : 3 ≤ n) (σ : K ≃+* K) (a : K) {x : Fin (2 * n) → K}
    (hx : polar (coordinateQuadPlus n K) x (pvec ⟨1, by omega⟩ true) = 0) :
    Matrix.mulVec ((spinModelPlus hn (ySpin hn σ a) : GL (Fin (2 * n)) K) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) K) x =
      x - (σ a * polar (coordinateQuadPlus n K) x (pvec ⟨0, by omega⟩ false) +
        a * polar (coordinateQuadPlus n K) x (pvec ⟨0, by omega⟩ true)) •
          pvec ⟨1, by omega⟩ true := by
  have h01 := zero_ne_one_idx (n := n) hn
  have p1 : polar (coordinateQuadPlus n K) (pvec (K := K) ⟨1, by omega⟩ true)
      (pvec ⟨1, by omega⟩ true) = 0 := polar_pvec_self _ _
  have p2 : polar (coordinateQuadPlus n K) (pvec (K := K) ⟨1, by omega⟩ true)
      (pvec ⟨0, by omega⟩ true) = 0 := polar_pvec_of_ne h01.symm _ _
  rw [ySpin, map_mul, mulVec_mul, spinModelPlus_longRoot_eichler, spinModelPlus_longRoot_eichler]
  simp only [eichlerC, polar_sub_left, polar_smul_left, polar_smul_right,
    QuadraticMap.map_smul, form_pvec, hx, p1, p2, smul_eq_mul, mul_zero, zero_smul,
    add_zero, sub_zero]
  module

omit [Finite K] [CharP K 2] in
theorem ySpin_mulVec_f₁ (hn : 3 ≤ n) (σ : K ≃+* K) (a : K) :
    Matrix.mulVec ((spinModelPlus hn (ySpin hn σ a) : GL (Fin (2 * n)) K) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) K) (pvec ⟨1, by omega⟩ false) =
      pvec ⟨1, by omega⟩ false + a • pvec ⟨0, by omega⟩ true + σ a • pvec ⟨0, by omega⟩ false -
        (a * σ a) • pvec ⟨1, by omega⟩ true := by
  have h01 := zero_ne_one_idx (n := n) hn
  have p1 : polar (coordinateQuadPlus n K) (pvec (K := K) ⟨1, by omega⟩ false)
      (pvec ⟨1, by omega⟩ true) = 1 := polar_pvec_not _ false
  have p2 : polar (coordinateQuadPlus n K) (pvec (K := K) ⟨1, by omega⟩ false)
      (pvec ⟨0, by omega⟩ false) = 0 := polar_pvec_of_ne h01.symm _ _
  have p3 : polar (coordinateQuadPlus n K) (pvec (K := K) ⟨0, by omega⟩ false)
      (pvec ⟨1, by omega⟩ true) = 0 := polar_pvec_of_ne h01 _ _
  have p4 : polar (coordinateQuadPlus n K) (pvec (K := K) ⟨1, by omega⟩ false)
      (pvec ⟨0, by omega⟩ true) = 0 := polar_pvec_of_ne h01.symm _ _
  have p5 : polar (coordinateQuadPlus n K) (pvec (K := K) ⟨0, by omega⟩ false)
      (pvec ⟨0, by omega⟩ true) = 1 := polar_pvec_not _ false
  have p6 : polar (coordinateQuadPlus n K) (pvec (K := K) ⟨1, by omega⟩ true)
      (pvec ⟨1, by omega⟩ true) = 0 := polar_pvec_self _ _
  have p7 : polar (coordinateQuadPlus n K) (pvec (K := K) ⟨1, by omega⟩ true)
      (pvec ⟨0, by omega⟩ true) = 0 := polar_pvec_of_ne h01.symm _ _
  rw [ySpin, map_mul, mulVec_mul, spinModelPlus_longRoot_eichler, spinModelPlus_longRoot_eichler]
  simp only [eichlerC, polar_add_left, polar_smul_left, polar_smul_right,
    QuadraticMap.map_smul, form_pvec, p1, p2, p3, p4, p5, smul_eq_mul, mul_zero,
    zero_smul, add_zero, sub_zero, zero_add, mul_one, one_smul]
  module

theorem exists_ne_zero_ne_ne (hn : 4 ≤ n) (a b : Fin n) :
    ∃ c : Fin n, c ≠ ⟨0, by omega⟩ ∧ c ≠ a ∧ c ≠ b := by
  have : ∃ m : ℕ, 1 ≤ m ∧ m ≤ 3 ∧ m ≠ a.val ∧ m ≠ b.val := by
    by_cases h1 : 1 ≠ a.val ∧ 1 ≠ b.val
    · exact ⟨1, le_rfl, by norm_num, h1⟩
    by_cases h2 : 2 ≠ a.val ∧ 2 ≠ b.val
    · exact ⟨2, by norm_num, by norm_num, h2⟩
    exact ⟨3, by norm_num, le_rfl, by omega, by omega⟩
  obtain ⟨m, hm1, hm3, ha, hb⟩ := this
  refine ⟨⟨m, by omega⟩, fun h => ?_, fun h => ha (congrArg Fin.val h),
    fun h => hb (congrArg Fin.val h)⟩
  have := congrArg Fin.val h
  simp only at this
  omega

omit [Finite K] in
theorem exists_sigma_comb_ne_zero {σ : K ≃+* K} (hσ1 : σ ≠ 1) {α β : K} (h : α ≠ 0 ∨ β ≠ 0) :
    ∃ a : K, σ a * β + a * α ≠ 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨θ, hθ⟩ : ∃ θ : K, σ θ ≠ θ := by
    by_contra h'
    push Not at h'
    exact hσ1 (RingEquiv.ext h')
  by_cases hs : β + α = 0
  · have hba : β = α := by linear_combination hs - α * h2
    refine ⟨θ, ?_⟩
    rw [hba, ← add_mul]
    refine mul_ne_zero (fun h' => hθ ?_) ?_
    · linear_combination h' - θ * h2
    · rcases h with h | h
      · exact h
      · rwa [hba] at h
  · exact ⟨1, by rwa [map_one, one_mul, one_mul]⟩

theorem eq_bot_of_reflFieldAutP (hn4 : 4 ≤ n) {σ : K ≃+* K} (hσσ : σ * σ = 1) (hσ1 : σ ≠ 1)
    (S : Subgroup (matrixDerived (coordinateQuadPlus n K))) (hS : IsPGroup 2 S)
    (hnorm : ∀ y, (plusRefl (K := K) (by omega : 1 ≤ n) * fieldAutP n σ :
      MulAut (matrixDerived (coordinateQuadPlus n K))) y = y → ∀ q ∈ S, y * q * y⁻¹ ∈ S) :
    S = ⊥ := by
  have hn : 3 ≤ n := by omega
  have h01 := zero_ne_one_idx (n := n) hn
  obtain ⟨x, hx0, hx⟩ := exists_fixed_ne_zero (by omega) S hS
  have hxW : x ∈ fixSpace S := hx
  have hW : ∀ i j : Fin n, i ≠ j → ∀ s t : Bool, i ≠ ⟨0, by omega⟩ → j ≠ ⟨0, by omega⟩ →
      ∀ y ∈ fixSpace S, eich i j s t y ∈ fixSpace S := by
    intro i j hij s t hi hj y hy
    have h := mulVec_mem_fixSpace hnorm (reflField_fix_longRoot hn σ hij hi hj s t) hy
    rwa [spinModelPlus_longRoot_mulVec, one_mul, one_mul] at h
  have hY : ∀ a : K, ∀ y ∈ fixSpace S, Matrix.mulVec ((spinModelPlus hn (ySpin hn σ a) :
      GL (Fin (2 * n)) K) : Matrix (Fin (2 * n)) (Fin (2 * n)) K) y ∈ fixSpace S :=
    fun a y hy => mulVec_mem_fixSpace hnorm (reflField_fix_ySpin hn hσσ a) hy
  have h3 := exists_ne_zero_ne_ne hn4
  obtain ⟨θ, hθ⟩ : ∃ θ : K, σ θ ≠ θ := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext h)
  have hu : pvec ⟨1, by omega⟩ true ∈ fixSpace S := by
    by_cases hc : ∃ k : Fin n, k ≠ ⟨0, by omega⟩ ∧ ∃ r,
        polar (coordinateQuadPlus n K) x (pvec k r) ≠ 0
    · obtain ⟨k, hk, r, hkr⟩ := hc
      exact spread (fixSpace S) (· ≠ ⟨0, by omega⟩) hW h3 hxW hk hkr _ _ h01.symm
    · push Not at hc
      have hx1 := hc _ h01.symm true
      have hαβ : polar (coordinateQuadPlus n K) x (pvec ⟨0, by omega⟩ true) ≠ 0 ∨
          polar (coordinateQuadPlus n K) x (pvec ⟨0, by omega⟩ false) ≠ 0 := by
        by_contra h
        push Not at h
        refine hx0 (eq_zero_of_polar_pvec fun k r => ?_)
        by_cases hk : k = ⟨0, by omega⟩
        · subst hk
          cases r
          · exact h.2
          · exact h.1
        · exact hc k hk r
      obtain ⟨a, ha⟩ := exists_sigma_comb_ne_zero hσ1 hαβ
      have h := (fixSpace S).neg_mem ((fixSpace S).sub_mem (hY a x hxW) hxW)
      rw [ySpin_mulVec_of_polar hn σ a hx1, sub_sub_cancel_left, neg_neg] at h
      have h' := (fixSpace S).smul_mem (σ a * polar (coordinateQuadPlus n K) x
        (pvec ⟨0, by omega⟩ false) + a * polar (coordinateQuadPlus n K) x
          (pvec ⟨0, by omega⟩ true))⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h'
  have hall := spread (fixSpace S) (· ≠ ⟨0, by omega⟩) hW h3 hu h01.symm
    (r := false) (by rw [polar_pvec]; simp)
  have hw : ∀ a : K, a • pvec ⟨0, by omega⟩ true + σ a • pvec ⟨0, by omega⟩ false ∈
      fixSpace S := by
    intro a
    have hf₁ := hall ⟨1, by omega⟩ false h01.symm
    have h := (fixSpace S).add_mem ((fixSpace S).sub_mem (hY a _ hf₁) hf₁)
      ((fixSpace S).smul_mem (a * σ a) hu)
    rw [ySpin_mulVec_f₁] at h
    convert h using 1
    abel
  have hf₀ : pvec (K := K) ⟨0, by omega⟩ false ∈ fixSpace S := by
    have h := (fixSpace S).sub_mem ((fixSpace S).smul_mem θ (hw 1)) (hw θ)
    rw [map_one, one_smul, one_smul, smul_add, add_sub_add_left_eq_sub, ← sub_smul] at h
    have h' := (fixSpace S).smul_mem (θ - σ θ)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hθ)), one_smul] at h'
  have he₀ : pvec (K := K) ⟨0, by omega⟩ true ∈ fixSpace S := by
    have h := (fixSpace S).sub_mem (hw 1) hf₀
    rwa [map_one, one_smul, one_smul, add_sub_cancel_right] at h
  have htop : fixSpace S = ⊤ := eq_top_of_pvec_mem fun k r => by
    by_cases hk : k = ⟨0, by omega⟩
    · subst hk
      cases r
      · exact hf₀
      · exact he₀
    · exact hall k r hk
  refine eq_bot_of_fix_top S fun q hq y => ?_
  have hy : y ∈ fixSpace S := htop ▸ Submodule.mem_top
  exact hy q hq

end GraphField

end AutOm

end CFSG.StandardType
