module

public import CFSG.RankThree.PartTwo.Toolkit.Statements
public import CFSG.RankThree.PartTwo.Toolkit.Cocycle
public meta import CFSG.RankThree.PartTwo.Toolkit.Raw
public meta import CFSG.RankThree.PartTwo.Toolkit.Cocycle
public import CFSG.RankThree.PartTwo.Toolkit.H1Inputs
public import Certificates.Certificate8173

public section

namespace CFSG.RankThree.PartTwo.Toolkit

open Raw Subgroup
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

local notation "SL33" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)

@[expose] def slAinv : SL33 := ⟨!![1, 2, 0; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def slBinv : SL33 := ⟨!![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide⟩

theorem slA_inv : slA⁻¹ = slAinv :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (by decide))

theorem slB_inv : slB⁻¹ = slBinv :=
  inv_eq_of_mul_eq_one_right (Subtype.ext (by decide))

theorem closure_slA_slB :
    Subgroup.closure {y : SL33 | y ∈ [slA, slB]} = ⊤ :=
  Certificates.certificate8173

@[expose] def relators : List Word :=
  [[(false, 3)], [(true, 3)],
    [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1),
      (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1)],
    [(false, 1), (true, 1), (false, 1), (true, 2), (false, 1), (true, 1), (false, 1), (true, 2),
      (false, 1), (true, 1), (false, 1), (true, 2)],
    [(false, 1), (true, 1), (false, 2), (true, 2), (false, 1), (true, 1), (false, 2), (true, 2),
      (false, 1), (true, 1), (false, 2), (true, 2)]]

theorem relators_raw : ∀ w ∈ relators, evalRaw (ofMat (slA : Matrix (Fin 3) (Fin 3) (ZMod 3)))
    (ofMat (slB : Matrix (Fin 3) (Fin 3) (ZMod 3))) w = rone := by
  decide +kernel

theorem relators_eq_one : ∀ w ∈ relators, evalWord slA slB w = 1 :=
  fun w hw => evalWord_eq_one_SL (relators_raw w hw)

@[expose] def foxCheck (A B : R9) : Bool :=
  allV3.all fun x₁ => allV3.all fun x₂ =>
    !(relators.all fun w => foxRaw A B x₁ x₂ w == vzero) ||
      allV3.any fun m => x₁ == vsub (rmv A m) m && x₂ == vsub (rmv B m) m

theorem foxCheck_nat : foxCheck (ofMat (slA : Matrix (Fin 3) (Fin 3) (ZMod 3)))
    (ofMat (slB : Matrix (Fin 3) (Fin 3) (ZMod 3))) = true := by
  decide +kernel

theorem foxCheck_dual : foxCheck (ofMat ((slAinv : Matrix (Fin 3) (Fin 3) (ZMod 3))ᵀ))
    (ofMat ((slBinv : Matrix (Fin 3) (Fin 3) (ZMod 3))ᵀ)) = true := by
  decide +kernel

@[expose] def AllCoboundary {Y : Type*} [Group Y]
    (σ : Representation (ZMod 3) Y (Fin 3 → ZMod 3)) : Prop :=
  ∀ c : Y → Fin 3 → ZMod 3, IsCocycle σ c → ∃ m, ∀ y, c y = σ y m - m

theorem allCoboundary_of_foxCheck
    {Y : Type*} [Group Y] (φ : Y ≃* SL33)
    {σ : Representation (ZMod 3) Y (Fin 3 → ZMod 3)} {A B : Matrix (Fin 3) (Fin 3) (ZMod 3)}
    (hA : ∀ v, σ (φ.symm slA) v = A *ᵥ v) (hB : ∀ v, σ (φ.symm slB) v = B *ᵥ v)
    (hchk : foxCheck (ofMat A) (ofMat B) = true) : AllCoboundary σ := by
  intro c hc
  have hrel : ∀ w ∈ relators, evalWord (φ.symm slA) (φ.symm slB) w = 1 := fun w hw => by
    rw [show evalWord (φ.symm slA) (φ.symm slB) w = φ.symm (evalWord slA slB w) from
      (map_evalWord φ.symm.toMonoidHom slA slB w).symm, relators_eq_one w hw, map_one]
  have hfox : relators.all (fun w => foxRaw (ofMat A) (ofMat B) (ofVec (c (φ.symm slA)))
      (ofVec (c (φ.symm slB))) w == vzero) = true := by
    rw [List.all_eq_true]
    intro w hw
    rw [beq_iff_eq]
    exact hc.foxRaw_eq_zero hA hB (hrel w hw)
  simp only [foxCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
    Bool.and_eq_true, beq_iff_eq] at hchk
  obtain ⟨m, -, hm₁, hm₂⟩ := (hchk _ (mem_allV3 _) _ (mem_allV3 _)).resolve_left (by
    rw [hfox]; exact Bool.noConfusion)
  refine ⟨toVec m, fun y => ?_⟩
  have hgen : Subgroup.closure {y : Y | y ∈ [φ.symm slA, φ.symm slB]} = ⊤ := by
    have h := congrArg (Subgroup.map φ.symm.toMonoidHom) closure_slA_slB
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ φ.symm.surjective] at h
    rw [← h]
    congr 1
    ext y
    simp [eq_comm]
  have heq := hc.eq_of_closure_eq_top (isCocycle_coboundary (σ := σ) (toVec m)) hgen (by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · apply ofVec_injective
      rw [ofVec_sub, hA, ofVec_mulVec, ofVec_toVec, hm₁]
    · apply ofVec_injective
      rw [ofVec_sub, hB, ofVec_mulVec, ofVec_toVec, hm₂])
  exact congrFun heq y

section H1

variable {Y : Type*} [Group Y]

theorem natRepVia_apply (φ : Y →* SL33) (y : Y) (v : Fin 3 → ZMod 3) :
    natRepVia φ y v = (φ y : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v :=
  Matrix.toLin'_apply _ _

theorem dualRepVia_apply (φ : Y →* SL33) (y : Y) (v : Fin 3 → ZMod 3) :
    dualRepVia φ y v = (φ y⁻¹ : Matrix (Fin 3) (Fin 3) (ZMod 3))ᵀ *ᵥ v :=
  Matrix.toLin'_apply _ _

theorem coboundary_nat
    (φ : Y ≃* SL33) : AllCoboundary (natRepVia φ.toMonoidHom) :=
  allCoboundary_of_foxCheck φ (A := slA) (B := slB)
    (fun v => by rw [natRepVia_apply]; simp)
    (fun v => by rw [natRepVia_apply]; simp) foxCheck_nat

theorem coboundary_dual
    (φ : Y ≃* SL33) : AllCoboundary (dualRepVia φ.toMonoidHom) :=
  allCoboundary_of_foxCheck φ (A := (slAinv : Matrix (Fin 3) (Fin 3) (ZMod 3))ᵀ)
    (B := (slBinv : Matrix (Fin 3) (Fin 3) (ZMod 3))ᵀ)
    (fun v => by
      rw [dualRepVia_apply, ← map_inv, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        slA_inv])
    (fun v => by
      rw [dualRepVia_apply, ← map_inv, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
        slB_inv])
    foxCheck_dual

end H1

end CFSG.RankThree.PartTwo.Toolkit
