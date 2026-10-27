module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmMinusOuter
import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaMinusModel
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog516CSpin

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open Module QuadraticMap

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private noncomputable def omT1 (b c : K) : Vm 4 K ≃ₗ[K] Vm 4 K :=
  CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (planeVec 4 ![1, 0])

private noncomputable def omW (b c : K) : Vm 4 K ≃ₗ[K] Vm 4 K :=
  CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (eVec 4 0 + fVec 4 0) *
    CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (eVec 4 1 + fVec 4 1)

private noncomputable def omT3 (b c : K) : Vm 4 K ≃ₗ[K] Vm 4 K := omW b c * omT1 b c

variable {b c : K} (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)

private def omA (K : Type) [Field K] : Vm 4 K := planeVec 4 (planeOne : Fin 2 → K)

private def omV2 (K : Type) [Field K] : Vm 4 K := eVec 4 0 + fVec 4 0

private def omV3 (K : Type) [Field K] : Vm 4 K := eVec 4 1 + fVec 4 1

omit [Finite K] in
private theorem reflect_apply_of_map_eq_one {b c : K} {v x : Vm 4 K}
    (hv : quadMinus 4 K b c v = 1) :
    CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) v x =
      x + polar (quadMinus 4 K b c) v x • v := by
  have hv0 : quadMinus 4 K b c v ≠ 0 := by rw [hv]; exact one_ne_zero
  rw [CFSG.ClassicalGroups.Orthogonal.reflect_apply hv0, hv, div_one, sub_eq_add_neg,
    ← neg_smul, CharTwo.neg_eq]

omit [CharP K 2] [Finite K] in
private theorem quadMinus_omA {b c : K} : quadMinus 4 K b c (omA K) = 1 :=
  quadMinus_planeOne (n := 4) (b := b) (c := c)

omit [CharP K 2] [Finite K] in
private theorem quadMinus_omV2 {b c : K} : quadMinus 4 K b c (omV2 K) = 1 := by
  rw [omV2, QuadraticMap.map_add (quadMinus 4 K b c), quadMinus_eVec, quadMinus_fVec,
    polar_eVec_fVec]
  norm_num

omit [CharP K 2] [Finite K] in
private theorem quadMinus_omV3 {b c : K} : quadMinus 4 K b c (omV3 K) = 1 := by
  rw [omV3, QuadraticMap.map_add (quadMinus 4 K b c), quadMinus_eVec, quadMinus_fVec,
    polar_eVec_fVec]
  norm_num

omit [CharP K 2] [Finite K] in
private theorem polar_omV2_omV3 {b c : K} : polar (quadMinus 4 K b c) (omV2 K) (omV3 K) = 0 := by
  rw [omV2, omV3, polar_add_left, polar_add_right, polar_add_right, polar_eVec_eVec,
    polar_eVec_fVec, polar_fVec_eVec, polar_fVec_fVec]
  norm_num

omit [CharP K 2] [Finite K] in
private theorem polar_omV2_eVec_zero {b c : K} :
    polar (quadMinus 4 K b c) (omV2 K) (eVec 4 0) = 1 := by
  rw [omV2, polar_add_left, polar_eVec_eVec, polar_fVec_eVec]
  norm_num

omit [CharP K 2] [Finite K] in
private theorem polar_omV2_eVec_one {b c : K} :
    polar (quadMinus 4 K b c) (omV2 K) (eVec 4 1) = 0 := by
  rw [omV2, polar_add_left, polar_eVec_eVec, polar_fVec_eVec]
  norm_num

omit [CharP K 2] [Finite K] in
private theorem polar_omV3_eVec_zero {b c : K} :
    polar (quadMinus 4 K b c) (omV3 K) (eVec 4 0) = 0 := by
  rw [omV3, polar_add_left, polar_eVec_eVec, polar_fVec_eVec]
  norm_num

omit [CharP K 2] [Finite K] in
private theorem polar_omV3_eVec_one {b c : K} :
    polar (quadMinus 4 K b c) (omV3 K) (eVec 4 1) = 1 := by
  rw [omV3, polar_add_left, polar_eVec_eVec, polar_fVec_eVec]
  norm_num

omit [CharP K 2] [Finite K] in
private theorem polar_omV2_planeVec (b c : K) (p : Fin 2 → K) :
    polar (quadMinus 4 K b c) (omV2 K) (planeVec 4 p) = 0 := by
  rw [omV2, polar_add_left, polar_eVec_planeVec, polar_fVec_planeVec, add_zero]

omit [CharP K 2] [Finite K] in
private theorem polar_omV3_planeVec (b c : K) (p : Fin 2 → K) :
    polar (quadMinus 4 K b c) (omV3 K) (planeVec 4 p) = 0 := by
  rw [omV3, polar_add_left, polar_eVec_planeVec, polar_fVec_planeVec, add_zero]

omit [CharP K 2] [Finite K] in
private theorem polar_omA_omV2 (b c : K) : polar (quadMinus 4 K b c) (omA K) (omV2 K) = 0 := by
  rw [omA, omV2, polar_add_right, polar_planeVec_eVec, polar_planeVec_fVec, add_zero]

omit [CharP K 2] [Finite K] in
private theorem polar_omA_omV3 (b c : K) : polar (quadMinus 4 K b c) (omA K) (omV3 K) = 0 := by
  rw [omA, omV3, polar_add_right, polar_planeVec_eVec, polar_planeVec_fVec, add_zero]

omit [Finite K] in
private theorem polar_omA_single (b c : K) :
    polar (quadMinus 4 K b c) (omA K) (planeVec 4 (Pi.single (1 : Fin 2) 1)) = b := by
  rw [omA, polar_planeVec_planeVec, polarPlane]
  simp [planeOne, CharTwo.two_eq_zero]

omit [Finite K] in
private theorem omT1_apply (b c : K) (y : Vm 4 K) :
    omT1 b c y = y + polar (quadMinus 4 K b c) (omA K) y • omA K :=
  reflect_apply_of_map_eq_one (b := b) (c := c) (v := omA K) quadMinus_omA

omit [Finite K] in
private theorem omT1_eVec_zero (b c : K) : omT1 b c (eVec 4 0) = eVec 4 0 := by
  rw [omT1_apply, omA, polar_planeVec_eVec, zero_smul, add_zero]

omit [Finite K] in
private theorem omT1_eVec_one (b c : K) : omT1 b c (eVec 4 1) = eVec 4 1 := by
  rw [omT1_apply, omA, polar_planeVec_eVec, zero_smul, add_zero]

omit [Finite K] in
private theorem omT1_planeSingle (b c : K) :
    omT1 b c (planeVec 4 (Pi.single (1 : Fin 2) 1)) =
      planeVec 4 (Pi.single (1 : Fin 2) 1) + b • omA K := by
  rw [omT1_apply, polar_omA_single]

omit [CharP K 2] [Finite K] in
private theorem omT1_commute_omV2 (b c : K) :
    omT1 b c * CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV2 K) =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV2 K) * omT1 b c :=
  CFSG.StandardType.RootCentOmega.reflect_mul_reflect_comm (polar_omA_omV2 b c)

omit [CharP K 2] [Finite K] in
private theorem omT1_commute_omV3 (b c : K) :
    omT1 b c * CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV3 K) =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV3 K) * omT1 b c :=
  CFSG.StandardType.RootCentOmega.reflect_mul_reflect_comm (polar_omA_omV3 b c)

omit [CharP K 2] [Finite K] in
private theorem omV2_commute_omV3 (b c : K) :
    CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV2 K) *
        CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV3 K) =
      CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV3 K) *
        CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV2 K) :=
  CFSG.StandardType.RootCentOmega.reflect_mul_reflect_comm polar_omV2_omV3

omit [Finite K] in
private theorem omW_apply (b c : K) (y : Vm 4 K) :
    omW b c y = y + polar (quadMinus 4 K b c) (omV2 K) y • omV2 K +
      polar (quadMinus 4 K b c) (omV3 K) y • omV3 K := by
  rw [omW, LinearEquiv.mul_apply,
    show (eVec 4 1 + fVec 4 1 : Vm 4 K) = omV3 K from rfl,
    show (eVec 4 0 + fVec 4 0 : Vm 4 K) = omV2 K from rfl,
    reflect_apply_of_map_eq_one (b := b) (c := c) (v := omV3 K) (x := y) quadMinus_omV3,
    reflect_apply_of_map_eq_one (b := b) (c := c) (v := omV2 K)
      (x := y + polar (quadMinus 4 K b c) (omV3 K) y • omV3 K) quadMinus_omV2,
    polar_add_right, polar_smul_right, polar_omV2_omV3, smul_zero, add_zero]
  abel

omit [Finite K] in
private theorem omW_eVec_zero (b c : K) : omW b c (eVec 4 0) = fVec 4 0 := by
  rw [omW_apply, polar_omV2_eVec_zero, polar_omV3_eVec_zero, one_smul, zero_smul, add_zero,
    omV2, ← add_assoc, CFSG.RankThree.OrthogonalInvolutions.add_self_vec K, zero_add]

omit [Finite K] in
private theorem omW_eVec_one (b c : K) : omW b c (eVec 4 1) = fVec 4 1 := by
  rw [omW_apply, polar_omV2_eVec_one, polar_omV3_eVec_one, one_smul, zero_smul, add_zero,
    omV3, ← add_assoc, CFSG.RankThree.OrthogonalInvolutions.add_self_vec K, zero_add]

omit [CharP K 2] [Finite K] in
private theorem omW_mem (b c : K) :
    omW b c ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) :=
  mul_mem (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup _ _)
    (CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup _ _)

omit [CharP K 2] [Finite K] in
private theorem omW_mul_self (b c : K) : omW b c * omW b c = 1 := by
  have h2 := CFSG.ClassicalGroups.Orthogonal.reflect_mul_self (quadMinus 4 K b c) (omV2 K)
  have h3 := CFSG.ClassicalGroups.Orthogonal.reflect_mul_self (quadMinus 4 K b c) (omV3 K)
  have hc := omV2_commute_omV3 b c
  set A := CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV2 K)
  set B := CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV3 K)
  change A * B * (A * B) = 1
  calc A * B * (A * B) = A * (B * A) * B := by group
    _ = A * (A * B) * B := by rw [← hc]
    _ = (A * A) * (B * B) := by group
    _ = 1 := by rw [h2, h3, one_mul]

omit [CharP K 2] [Finite K] in
private theorem omT1_mem (b c : K) :
    omT1 b c ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) :=
  CFSG.ClassicalGroups.Orthogonal.reflect_mem_orthogonalGroup _ _

omit [CharP K 2] [Finite K] in
private theorem omT1_mul_self (b c : K) : omT1 b c * omT1 b c = 1 :=
  CFSG.ClassicalGroups.Orthogonal.reflect_mul_self _ _

omit [CharP K 2] [Finite K] in
private theorem omT3_mem (b c : K) :
    omT3 b c ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) :=
  mul_mem (omW_mem b c) (omT1_mem b c)

omit [CharP K 2] [Finite K] in
private theorem omT1_commute_omW (b c : K) : omT1 b c * omW b c = omW b c * omT1 b c := by
  have hc2 := omT1_commute_omV2 b c
  have hc3 := omT1_commute_omV3 b c
  set T := omT1 b c
  set A := CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV2 K)
  set B := CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (omV3 K)
  have hTA : T * A = A * T := hc2
  have hTB : T * B = B * T := hc3
  change T * (A * B) = A * B * T
  calc T * (A * B) = (T * A) * B := by group
    _ = (A * T) * B := by rw [hTA]
    _ = A * (T * B) := by group
    _ = A * (B * T) := by rw [hTB]
    _ = A * B * T := by group

omit [CharP K 2] [Finite K] in
private theorem omT3_mul_self (b c : K) : omT3 b c * omT3 b c = 1 := by
  have h1 := omT1_mul_self b c
  have hw := omW_mul_self b c
  have hcomm := omT1_commute_omW b c
  rw [omT3]
  calc (omW b c * omT1 b c) * (omW b c * omT1 b c)
      = omW b c * (omT1 b c * omW b c) * omT1 b c := by group
    _ = omW b c * (omW b c * omT1 b c) * omT1 b c := by rw [hcomm]
    _ = (omW b c * omW b c) * (omT1 b c * omT1 b c) := by group
    _ = 1 := by rw [hw, h1, one_mul]

omit [Finite K] in
private theorem omT3_eVec_zero (b c : K) : omT3 b c (eVec 4 0) = fVec 4 0 := by
  rw [omT3, LinearEquiv.mul_apply, omT1_eVec_zero, omW_eVec_zero]

omit [Finite K] in
private theorem omT3_eVec_one (b c : K) : omT3 b c (eVec 4 1) = fVec 4 1 := by
  rw [omT3, LinearEquiv.mul_apply, omT1_eVec_one, omW_eVec_one]

omit [Finite K] in
private theorem omT3_planeSingle (b c : K) :
    omT3 b c (planeVec 4 (Pi.single (1 : Fin 2) 1)) =
      planeVec 4 (Pi.single (1 : Fin 2) 1) + b • omA K := by
  rw [omT3, LinearEquiv.mul_apply, omT1_planeSingle, omW_apply, omA, polar_add_right,
    polar_add_right, polar_smul_right, polar_smul_right, polar_omV2_planeVec,
    polar_omV2_planeVec, polar_omV3_planeVec, polar_omV3_planeVec]
  simp

omit [CharP K 2] in
private theorem finrank_commSpace_omT1 (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    finrank K (commSpace (omT1 b c)) = 1 := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ
  have hQa : quadMinus 4 K b c (planeVec 4 ![1, 0]) = 1 := by
    rw [quadMinus_planeVec]
    norm_num
  let _ : Invertible (quadMinus 4 K b c (planeVec 4 ![1, 0])) := by
    rw [hQa]; exact invertibleOne
  rw [omT1, CFSG.ClassicalGroups.Orthogonal.reflect_eq_reflection]
  exact CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ
    (planeVec 4 ![1, 0])

omit [Finite K] in
private theorem omT3_le_span (b c : K) :
    commSpace (omT3 b c) ≤ Submodule.span K ({omA K, omV2 K, omV3 K} : Set (Vm 4 K)) := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_commSpace.mp hx
  have himg : omT3 b c y = y + (polar (quadMinus 4 K b c) (omA K) y • omA K +
      (polar (quadMinus 4 K b c) (omV2 K) (omT1 b c y) • omV2 K +
        polar (quadMinus 4 K b c) (omV3 K) (omT1 b c y) • omV3 K)) := by
    rw [omT3, LinearEquiv.mul_apply, omT1_apply, omW_apply]
    abel
  rw [himg, CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec K]
  have hcancel : (y + (polar (quadMinus 4 K b c) (omA K) y • omA K +
      (polar (quadMinus 4 K b c) (omV2 K) (omT1 b c y) • omV2 K +
        polar (quadMinus 4 K b c) (omV3 K) (omT1 b c y) • omV3 K))) + y =
      polar (quadMinus 4 K b c) (omA K) y • omA K +
      (polar (quadMinus 4 K b c) (omV2 K) (omT1 b c y) • omV2 K +
        polar (quadMinus 4 K b c) (omV3 K) (omT1 b c y) • omV3 K) := by
    rw [add_comm (y + _) y, ← add_assoc, add_comm y y,
      CFSG.RankThree.OrthogonalInvolutions.add_self_vec K, zero_add]
  rw [hcancel]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))

omit [Finite K] in
private theorem omV2_mem_commSpace_omT3 (b c : K) : omV2 K ∈ commSpace (omT3 b c) :=
  mem_commSpace.mpr ⟨eVec 4 0, by
    rw [omT3_eVec_zero, CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec K, omV2,
      add_comm]⟩

omit [Finite K] in
private theorem omV3_mem_commSpace_omT3 (b c : K) : omV3 K ∈ commSpace (omT3 b c) :=
  mem_commSpace.mpr ⟨eVec 4 1, by
    rw [omT3_eVec_one, CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec K, omV3,
      add_comm]⟩

private theorem omA_mem_commSpace_omT3 (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    omA K ∈ commSpace (omT3 b c) := by
  have hb : b ≠ 0 := CFSG.StandardType.GGOppRadOmega.b_ne_zero hirrQ
  have h : omT3 b c (planeVec 4 (Pi.single (1 : Fin 2) 1)) -
      planeVec 4 (Pi.single (1 : Fin 2) 1) = b • omA K := by
    rw [omT3_planeSingle, CFSG.RankThree.OrthogonalInvolutions.sub_eq_add_vec K,
      add_comm (planeVec 4 (Pi.single (1 : Fin 2) 1) + b • omA K)
        (planeVec 4 (Pi.single (1 : Fin 2) 1)),
      ← add_assoc, CFSG.RankThree.OrthogonalInvolutions.add_self_vec K, zero_add]
  have hmem : b • omA K ∈ commSpace (omT3 b c) :=
    mem_commSpace.mpr ⟨planeVec 4 (Pi.single (1 : Fin 2) 1), h⟩
  have := Submodule.smul_mem (commSpace (omT3 b c)) b⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at this

omit [CharP K 2] [Finite K] in
private theorem linearIndependent_omA_omV :
    LinearIndependent K ![omA K, omV2 K, omV3 K] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 := congrFun hg (.inr (.inr 0))
  have h1 := congrFun hg (.inl 0)
  have h2 := congrFun hg (.inl 1)
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
  simp [omA, omV2, omV3, planeOne, planeVec, eVec, fVec] at h0 h1 h2
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem finrank_commSpace_omT3 (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    finrank K (commSpace (omT3 b c)) = 3 := by
  have heq : commSpace (omT3 b c) = Submodule.span K ({omA K, omV2 K, omV3 K} : Set (Vm 4 K)) := by
    refine le_antisymm (omT3_le_span b c) ?_
    refine Submodule.span_le.mpr ?_
    rintro x (rfl | rfl | rfl)
    · exact omA_mem_commSpace_omT3 hirrQ
    · exact omV2_mem_commSpace_omT3 b c
    · exact omV3_mem_commSpace_omT3 b c
  rw [heq]
  have hfr := finrank_span_eq_card (linearIndependent_omA_omV (K := K))
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.singleton_union, Set.singleton_union, Fintype.card_fin] at hfr
  exact hfr

private theorem omT1_ne_one (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : omT1 b c ≠ 1 := by
  have hb : b ≠ 0 := CFSG.StandardType.GGOppRadOmega.b_ne_zero hirrQ
  intro h
  have h' := congrFun (congrArg (fun e : Vm 4 K ≃ₗ[K] Vm 4 K =>
    e (planeVec 4 (Pi.single (1 : Fin 2) 1))) h) (.inr (.inr 0))
  rw [omT1_planeSingle] at h'
  simp [omA, planeOne, planeVec] at h'
  exact hb h'

omit [Finite K] in
private theorem omT3_ne_one (b c : K) : omT3 b c ≠ 1 := by
  intro h
  have h' : omT3 b c (eVec 4 0) = eVec 4 0 := by
    rw [h]
    rfl
  rw [omT3_eVec_zero] at h'
  have h'' := congrFun h' (.inl 0)
  simp [eVec, fVec] at h''

private theorem exists_spin_conj (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (α : MulAut (spinGroup (quadMinus 4 K b c))) {r t : Vm 4 K ≃ₗ[K] Vm 4 K}
    (hαr : ∀ g, spinAction (quadMinus 4 K b c) (α g) =
      r * spinAction (quadMinus 4 K b c) g * r⁻¹)
    (hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c))
    (hrsq : r * r = 1) (hrne : r ≠ 1)
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c))
    (htsq : t * t = 1) (htne : t ≠ 1)
    (hletter : suzukiLetter (quadMinus 4 K b c) t = suzukiLetter (quadMinus 4 K b c) r)
    (hrank : finrank K (commSpace t) = finrank K (commSpace r))
    (hrodd : Odd (finrank K (commSpace r))) :
    ∃ x : spinGroup (quadMinus 4 K b c), ∀ g,
      spinAction (quadMinus 4 K b c) (x⁻¹ * α (x * g * x⁻¹) * x) =
        t * spinAction (quadMinus 4 K b c) g * t⁻¹ := by
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ
  have hrord : orderOf r = 2 := orderOf_eq_prime (by rwa [pow_two]) hrne
  have htord : orderOf t = 2 := orderOf_eq_prime (by rwa [pow_two]) htne
  obtain ⟨y, hyO, hyconj⟩ :=
    (CFSG.RankThree.OrthogonalInvolutions.isConj_iff_suzukiLetter_eq hQ hrO hrord htO
      htord).mpr ⟨hletter, hrank⟩
  have hrletter : suzukiLetter (quadMinus 4 K b c) r = .b :=
    CFSG.RankThree.OrthogonalInvolutions.suzukiLetter_eq_b_iff.mpr hrodd
  have htodd : Odd (finrank K (commSpace t)) :=
    CFSG.RankThree.OrthogonalInvolutions.suzukiLetter_eq_b_iff.mp
      (by rw [hletter]; exact hrletter)
  have hex : ∃ u ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadMinus 4 K b c) hQ,
      u * r * u⁻¹ = t := by
    by_cases hy : y ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadMinus 4 K b c) hQ
    · exact ⟨y, hy, hyconj⟩
    · have hyodd : Odd (finrank K (commSpace y)) :=
        Nat.not_even_iff_odd.mp fun he =>
          hy ((CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup).mpr ⟨hyO, he⟩)
      refine ⟨t * y, ?_, ?_⟩
      · have htyO : t * y ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) :=
          mul_mem htO hyO
        have htyEven : Even (finrank K (commSpace (t * y))) := by
          rw [← ZMod.natCast_eq_zero_iff_even,
            CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ htO hyO,
            ZMod.natCast_eq_one_iff_odd.mpr htodd, ZMod.natCast_eq_one_iff_odd.mpr hyodd]
          decide
        exact (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup).mpr ⟨htyO, htyEven⟩
      · calc t * y * r * (t * y)⁻¹ = t * (y * r * y⁻¹) * t⁻¹ := by group
          _ = t * t * t⁻¹ := by rw [hyconj]
          _ = t := by rw [htsq, one_mul, inv_eq_of_mul_eq_one_left htsq]
  obtain ⟨u, huOmega, huconj⟩ := hex
  have huinvOmega : u⁻¹ ∈
      CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadMinus 4 K b c) hQ :=
    (CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadMinus 4 K b c) hQ).inv_mem huOmega
  obtain ⟨x, hx⟩ := CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_minus
    (n := 4) hirrQ (by norm_num) huinvOmega
  refine ⟨x, fun g => ?_⟩
  have hkey : (spinAction (quadMinus 4 K b c) x)⁻¹ * r * spinAction (quadMinus 4 K b c) x = t := by
    rw [hx, inv_inv]
    exact huconj
  calc spinAction (quadMinus 4 K b c) (x⁻¹ * α (x * g * x⁻¹) * x)
      = (spinAction (quadMinus 4 K b c) x)⁻¹ *
          spinAction (quadMinus 4 K b c) (α (x * g * x⁻¹)) *
            spinAction (quadMinus 4 K b c) x := by
        rw [map_mul, map_mul, map_inv]
    _ = (spinAction (quadMinus 4 K b c) x)⁻¹ *
          (r * spinAction (quadMinus 4 K b c) (x * g * x⁻¹) * r⁻¹) *
            spinAction (quadMinus 4 K b c) x := by rw [hαr]
    _ = (spinAction (quadMinus 4 K b c) x)⁻¹ *
          (r * (spinAction (quadMinus 4 K b c) x * spinAction (quadMinus 4 K b c) g *
            (spinAction (quadMinus 4 K b c) x)⁻¹) * r⁻¹) *
            spinAction (quadMinus 4 K b c) x := by rw [map_mul, map_mul, map_inv]
    _ = ((spinAction (quadMinus 4 K b c) x)⁻¹ * r * spinAction (quadMinus 4 K b c) x) *
          spinAction (quadMinus 4 K b c) g *
            ((spinAction (quadMinus 4 K b c) x)⁻¹ * r * spinAction (quadMinus 4 K b c) x)⁻¹ := by
        group
    _ = t * spinAction (quadMinus 4 K b c) g * t⁻¹ := by rw [hkey]

include hirrQ in
private theorem omMinus_two_outer_reduction_aux (hK : Nat.card K = 2)
    (α : MulAut (spinGroup (quadMinus 4 K b c))) (hα2 : α * α = 1)
    (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀) :
    ∃ x : spinGroup (quadMinus 4 K b c), ∃ t : Vm 4 K ≃ₗ[K] Vm 4 K,
      (t = omT1 b c ∨ t = omT3 b c) ∧ ∀ g,
        spinAction (quadMinus 4 K b c) (x⁻¹ * α (x * g * x⁻¹) * x) =
          t * spinAction (quadMinus 4 K b c) g * t⁻¹ := by
  classical
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite 4 K hirrQ
  obtain ⟨S, hS2, hconj⟩ :=
    SmallO8mCurtis.exists_isometry_of_involutive_aut hirrQ (e := 1) le_rfl
      (by rw [hK]; norm_num) α hα2
  let E := coordinateMinusIsometry 4 K (by norm_num : 1 ≤ 4) b c
  let r : Vm 4 K ≃ₗ[K] Vm 4 K :=
    (E.toLinearEquiv.trans (matrixLinearIso S.val)).trans E.symm.toLinearEquiv
  have hαr : ∀ g, spinAction (quadMinus 4 K b c) (α g) =
      r * spinAction (quadMinus 4 K b c) g * r⁻¹ :=
    SmallO8mCurtis.spinAction_conj_of_coordinate hirrQ α S hconj
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    change quadMinus 4 K b c (E.symm (matrixLinearIso S.val (E v))) = quadMinus 4 K b c v
    rw [E.symm.map_app]
    have hs := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp S.2 (E v)
    change coordinateQuadMinus 4 K (by norm_num) b c (matrixLinearIso S.val (E v)) =
      coordinateQuadMinus 4 K (by norm_num) b c (E v) at hs
    exact hs.trans (E.map_app v)
  have hrsq : r * r = 1 := by
    have hSval : ((S : GL (Fin 8) K) * (S : GL (Fin 8) K)) = 1 := by
      rw [← Subgroup.coe_mul, hS2]
      rfl
    have hM : matrixLinearIso S.val * matrixLinearIso S.val = 1 := by
      rw [← map_mul, hSval, map_one]
    have hMM : ∀ w : Fin (2 * 4) → K,
        matrixLinearIso S.val (matrixLinearIso S.val w) = w := by
      intro w
      have := congrArg (fun e : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K) => e w) hM
      simpa using this
    refine LinearEquiv.ext fun v => ?_
    change E.symm (matrixLinearIso S.val
      (E (E.symm (matrixLinearIso S.val (E v))))) = v
    rw [E.apply_symm_apply, hMM, E.symm_apply_apply]
  have hrne : r ≠ 1 := by
    intro hr1
    refine houter 1 ?_
    refine MulEquiv.ext fun g => ?_
    apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective (n := 4) hirrQ
    rw [hαr g, hr1, MulAut.conj_apply, map_mul, map_mul, map_inv]
    simp
  have hrnotOmega :
      r ∉ CFSG.RankThree.OrthogonalInvolutions.omegaGroup (quadMinus 4 K b c) hQ := by
    intro hmem
    obtain ⟨g₀, hg₀⟩ := CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_minus
      (n := 4) hirrQ (by norm_num) hmem
    refine houter g₀ ?_
    refine MulEquiv.ext fun g => ?_
    apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective (n := 4) hirrQ
    rw [hαr g, ← hg₀, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hlodd : Odd (finrank K (commSpace r)) :=
    Nat.not_even_iff_odd.mp fun he =>
      hrnotOmega ((CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup).mpr ⟨hrO, he⟩)
  have hbound : 2 * finrank K (commSpace r) ≤ 8 := by
    have h := CFSG.RankThree.OrthogonalInvolutions.two_mul_finrank_commSpace_le
      (V := Vm 4 K) (t := r) hrsq
    have hdim : finrank K (Vm 4 K) = 8 := by simp [Vm]
    omega
  have hl13 : finrank K (commSpace r) = 1 ∨ finrank K (commSpace r) = 3 := by
    obtain ⟨k, hk⟩ := hlodd
    omega
  have hrletter : suzukiLetter (quadMinus 4 K b c) r = .b :=
    CFSG.RankThree.OrthogonalInvolutions.suzukiLetter_eq_b_iff.mpr hlodd
  rcases hl13 with hl | hl
  · have hletter : suzukiLetter (quadMinus 4 K b c) (omT1 b c) =
        suzukiLetter (quadMinus 4 K b c) r := by
      rw [CFSG.RankThree.OrthogonalInvolutions.suzukiLetter_eq_b_iff.mpr (by
        rw [finrank_commSpace_omT1 hirrQ]; exact ⟨0, rfl⟩), hrletter]
    have hrank : finrank K (commSpace (omT1 b c)) = finrank K (commSpace r) := by
      rw [finrank_commSpace_omT1 hirrQ]; exact hl.symm
    obtain ⟨x, hx⟩ := exists_spin_conj hirrQ α hαr hrO hrsq hrne (omT1_mem b c)
      (omT1_mul_self b c) (omT1_ne_one hirrQ) hletter hrank hlodd
    exact ⟨x, omT1 b c, Or.inl rfl, hx⟩
  · have hletter : suzukiLetter (quadMinus 4 K b c) (omT3 b c) =
        suzukiLetter (quadMinus 4 K b c) r := by
      rw [CFSG.RankThree.OrthogonalInvolutions.suzukiLetter_eq_b_iff.mpr (by
        rw [finrank_commSpace_omT3 hirrQ]; exact ⟨1, rfl⟩), hrletter]
    have hrank : finrank K (commSpace (omT3 b c)) = finrank K (commSpace r) := by
      rw [finrank_commSpace_omT3 hirrQ]; exact hl.symm
    obtain ⟨x, hx⟩ := exists_spin_conj hirrQ α hαr hrO hrsq hrne (omT3_mem b c)
      (omT3_mul_self b c) (omT3_ne_one b c) hletter hrank hlodd
    exact ⟨x, omT3 b c, Or.inr rfl, hx⟩

include hirrQ in
theorem omMinus_two_outer_reduction (hK : Nat.card K = 2)
    (α : MulAut (spinGroup (quadMinus 4 K b c))) (hα2 : α * α = 1)
    (houter : ∀ g₀ : spinGroup (quadMinus 4 K b c), α ≠ MulAut.conj g₀) :
    ∃ x u : spinGroup (quadMinus 4 K b c),
      (u = 1 ∨ spinAction (quadMinus 4 K b c) u =
        CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (eVec 4 0 + fVec 4 0) *
          CFSG.ClassicalGroups.Orthogonal.reflect (quadMinus 4 K b c) (eVec 4 1 + fVec 4 1)) ∧
      ∀ g, x⁻¹ * α (x * g * x⁻¹) * x = u * o8mOuterAut hirrQ g * u⁻¹ := by
  obtain ⟨x, t, ht, hxt⟩ := omMinus_two_outer_reduction_aux hirrQ hK α hα2 houter
  have hβ : ∀ g, spinAction (quadMinus 4 K b c) (o8mOuterAut hirrQ g) =
      omT1 b c * spinAction (quadMinus 4 K b c) g * (omT1 b c)⁻¹ := fun g => by
    rw [spinAction_o8mOuterAut, o8mPlaneRefl_eq_reflect]
    rfl
  rcases ht with rfl | rfl
  · refine ⟨x, 1, Or.inl rfl, fun g => ?_⟩
    apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
    rw [hxt g, one_mul, inv_one, mul_one, hβ]
  · have hQ : quadMinus 4 K b c (eVec 4 0 + fVec 4 0) *
        quadMinus 4 K b c (eVec 4 1 + fVec 4 1) = 1 := by
      rw [show eVec 4 0 + fVec 4 0 = omV2 K from rfl, show eVec 4 1 + fVec 4 1 = omV3 K from rfl,
        quadMinus_omV2, quadMinus_omV3, one_mul]
    refine ⟨x, CFSG.ComponentClassification.GSThmB.Cent516.pairElt _ _ hQ,
      Or.inr (CFSG.ComponentClassification.GSThmB.Cent516.spinAction_pairElt hQ), fun g => ?_⟩
    apply CFSG.StandardType.RootCentOmega.spinAction_quadMinus_injective hirrQ
    rw [hxt g, map_mul, map_mul, map_inv,
      CFSG.ComponentClassification.GSThmB.Cent516.spinAction_pairElt hQ, hβ, omT3, omW,
      mul_inv_rev, mul_inv_rev]
    group

end CFSG.LocalAnalysis.WeakClosure81
