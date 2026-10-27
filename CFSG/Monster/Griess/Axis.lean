module

public import CFSG.Monster.Griess.Space
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice Matrix Module

@[expose] def ratVec (u : Fin 24 → ℤ) : Fin 24 → ℚ := fun i => (u i : ℚ)

@[expose] def projMat (u : Fin 24 → ℤ) : Matrix (Fin 24) (Fin 24) ℚ :=
  (32 : ℚ)⁻¹ • vecMulVec (ratVec u) (ratVec u)

theorem ratVec_neg (u : Fin 24 → ℤ) : ratVec (-u) = -ratVec u := by
  funext i
  simp [ratVec]

theorem ratVec_dotProduct_self {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    ratVec u ⬝ᵥ ratVec u = 32 := by
  have h := (mem_minVecs_iff.1 hu).2
  unfold normSq at h
  simp only [dotProduct, ratVec]
  exact_mod_cast h

theorem ratVec_ne_zero {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : ratVec u ≠ 0 := by
  intro h
  have := ratVec_dotProduct_self hu
  rw [h, dotProduct_zero] at this
  norm_num at this

theorem projMat_neg (u : Fin 24 → ℤ) : projMat (-u) = projMat u := by
  rw [projMat, projMat, ratVec_neg, neg_vecMulVec, vecMulVec_neg, neg_neg]

theorem transpose_projMat (u : Fin 24 → ℤ) : (projMat u)ᵀ = projMat u := by
  rw [projMat, transpose_smul, transpose_vecMulVec]

theorem projMat_mem_symMat (u : Fin 24 → ℤ) : projMat u ∈ symMat := transpose_projMat u

theorem projMat_mul_self {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    projMat u * projMat u = projMat u := by
  rw [projMat, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec,
    ratVec_dotProduct_self hu, vecMulVec_smul, smul_smul, smul_smul]
  norm_num

theorem trace_projMat {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : trace (projMat u) = 1 := by
  rw [projMat, trace_smul, trace_vecMulVec, ratVec_dotProduct_self hu, smul_eq_mul]
  norm_num

theorem vecMul_projMat (u : Fin 24 → ℤ) (v : Fin 24 → ℚ) :
    v ᵥ* projMat u = ((v ⬝ᵥ ratVec u) / 32) • ratVec u := by
  rw [projMat, vecMul_smul, vecMul_vecMulVec, smul_smul, div_eq_inv_mul]

theorem vecMul_projMat_self {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    ratVec u ᵥ* projMat u = ratVec u := by
  rw [vecMul_projMat, ratVec_dotProduct_self hu]
  norm_num

theorem range_vecMulLinear_projMat {u : Fin 24 → ℤ} (hu : u ∈ minVecs) :
    LinearMap.range (projMat u).vecMulLinear = Submodule.span ℚ {ratVec u} := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    rw [vecMulLinear_apply, vecMul_projMat]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact ⟨ratVec u, vecMul_projMat_self hu⟩

theorem vecMul_projMat_eq_zero_iff {u : Fin 24 → ℤ} (hu : u ∈ minVecs) (v : Fin 24 → ℚ) :
    v ᵥ* projMat u = 0 ↔ v ⬝ᵥ ratVec u = 0 := by
  rw [vecMul_projMat, smul_eq_zero, div_eq_zero_iff]
  have h1 : (32 : ℚ) ≠ 0 := by norm_num
  simp only [h1, or_false, ratVec_ne_zero hu]

theorem rank_projMat {u : Fin 24 → ℤ} (hu : u ∈ minVecs) : (projMat u).rank = 1 := by
  have h : LinearMap.range (projMat u).mulVecLin = LinearMap.range (projMat u).vecMulLinear := by
    congr 1
    apply LinearMap.ext
    intro v
    rw [mulVecLin_apply, vecMulLinear_apply, ← vecMul_transpose, transpose_projMat]
  rw [Matrix.rank, h, range_vecMulLinear_projMat hu, finrank_span_singleton (ratVec_ne_zero hu)]

@[expose] noncomputable def coordAxisE (p : C × Cocode) : symMat :=
  open Classical in
  if h : IsShortCoord p then ⟨projMat (uvec ⟨p, h⟩), projMat_mem_symMat _⟩ else 0

@[expose] noncomputable def axisE (r : Q) : symMat := coordAxisE (coordOf r)

@[expose] noncomputable def axis (r : Q) : SpaceB :=
  (2 : ℚ) • ((axisE r, 0, 0) : SpaceB) - (2 : ℚ) • ((0, Xlift r, 0) : SpaceB)

theorem coe_axisE {r : Q} (h : IsShortCoord (coordOf r)) :
    (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = projMat (uvec ⟨coordOf r, h⟩) := by
  unfold axisE coordAxisE
  rw [dite_eq_left h]

theorem axisE_eq_projMat {r : Q} (h : IsShortCoord (coordOf r)) {v : Fin 24 → ℤ}
    (hv : v ∈ minVecs) (hcl : classOf v = phi0 (coordOf r)) :
    (axisE r : Matrix (Fin 24) (Fin 24) ℚ) = projMat v := by
  rw [coe_axisE h]
  obtain ⟨hu, hclu, -⟩ := uvec_spec ⟨coordOf r, h⟩
  rcases (classOf_eq_iff hu hv).1 (hclu.trans hcl.symm) with h' | h'
  · rw [h']
  · rw [h', projMat_neg]

theorem symm_zQ_mul (r : Q) : spinEquiv.symm (zQ * r) = SpinCoord.z * spinEquiv.symm r :=
  (map_mul spinEquiv.symm zQ r).trans
    (congrArg (· * spinEquiv.symm r) (spinEquiv.symm_apply_apply SpinCoord.z))

theorem coordOf_zQ_mul (r : Q) : coordOf (zQ * r) = coordOf r :=
  (congrArg (fun x : SpinCoord => (x.a, x.δ)) (symm_zQ_mul r)).trans
    (Prod.ext (zero_add _) (zero_add _))

theorem centralCoord_zQ_mul (r : Q) : centralCoord (zQ * r) = centralCoord r + 1 := by
  have h := congrArg SpinCoord.s (symm_zQ_mul r)
  refine h.trans ?_
  change 1 + (spinEquiv.symm r).s + pair (spinEquiv.symm r).a 0 = centralCoord r + 1
  rw [pair_zero_right, add_zero, add_comm]
  rfl

theorem isShortCoord_zQ_mul {r : Q} (h : IsShortCoord (coordOf r)) :
    IsShortCoord (coordOf (zQ * r)) := by
  rw [coordOf_zQ_mul]
  exact h

private theorem sgn_add_one (s : ZMod 2) : sgn (s + 1) = -sgn s := by
  rw [sgn_add]
  change sgn s * (-1) = -sgn s
  ring

theorem Xlift_zQ_mul {r : Q} (h : IsShortCoord (coordOf r)) : Xlift (zQ * r) = -Xlift r := by
  have hc : (⟨coordOf (zQ * r), isShortCoord_zQ_mul h⟩ : ShortIdx) = ⟨coordOf r, h⟩ :=
    Subtype.ext (coordOf_zQ_mul r)
  rw [Xlift_eq (isShortCoord_zQ_mul h), Xlift_eq h, hc, centralCoord_zQ_mul, sgn_add_one,
    neg_smul]

theorem axisE_zQ_mul (r : Q) : axisE (zQ * r) = axisE r := congrArg coordAxisE (coordOf_zQ_mul r)

theorem axis_zQ_mul {r : Q} (h : IsShortCoord (coordOf r)) :
    axis (zQ * r) =
      (2 : ℚ) • ((axisE r, 0, 0) : SpaceB) + (2 : ℚ) • ((0, Xlift r, 0) : SpaceB) := by
  rw [axis, axisE_zQ_mul, Xlift_zQ_mul h, sub_eq_add_neg]
  congr 1
  ext <;> simp

theorem short_spin_axis_data (r : Q) (h : IsShortCoord (coordOf r)) :
    let u := ratVec (uvec ⟨coordOf r, h⟩)
    let E := (axisE r : Matrix (Fin 24) (Fin 24) ℚ)
    u ⬝ᵥ u = 32 ∧ E = (32 : ℚ)⁻¹ • vecMulVec u u ∧ Eᵀ = E ∧ E * E = E ∧ trace E = 1 ∧
    (∀ v : Fin 24 → ℚ, v ᵥ* E = ((v ⬝ᵥ u) / 32) • u) ∧ u ᵥ* E = u ∧
    LinearMap.range E.vecMulLinear = Submodule.span ℚ {u} ∧
    (∀ v : Fin 24 → ℚ, v ᵥ* E = 0 ↔ v ⬝ᵥ u = 0) ∧ E.rank = 1 ∧
    (∀ v ∈ minVecs, classOf v = phi0 (coordOf r) →
      E = (32 : ℚ)⁻¹ • vecMulVec (ratVec v) (ratVec v)) ∧
    axis r = (2 : ℚ) • ((axisE r, 0, 0) : SpaceB) - (2 : ℚ) • ((0, Xlift r, 0) : SpaceB) ∧
    IsShortCoord (coordOf (zQ * r)) ∧ coordOf (zQ * r) = coordOf r ∧ axisE (zQ * r) = axisE r ∧
    Xlift (zQ * r) = -Xlift r ∧
    axis (zQ * r) =
      (2 : ℚ) • ((axisE r, 0, 0) : SpaceB) + (2 : ℚ) • ((0, Xlift r, 0) : SpaceB) := by
  intro u E
  have hu := uvec_mem ⟨coordOf r, h⟩
  have hE : E = projMat (uvec ⟨coordOf r, h⟩) := coe_axisE h
  refine ⟨ratVec_dotProduct_self hu, hE, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl,
    isShortCoord_zQ_mul h, coordOf_zQ_mul r, axisE_zQ_mul r, Xlift_zQ_mul h, axis_zQ_mul h⟩
  · rw [hE]; exact transpose_projMat _
  · rw [hE]; exact projMat_mul_self hu
  · rw [hE]; exact trace_projMat hu
  · intro v; rw [hE]; exact vecMul_projMat _ v
  · rw [hE]; exact vecMul_projMat_self hu
  · rw [hE]; exact range_vecMulLinear_projMat hu
  · intro v; rw [hE]; exact vecMul_projMat_eq_zero_iff hu v
  · rw [hE]; exact rank_projMat hu
  · intro v hv hcl
    exact axisE_eq_projMat h hv hcl

end CFSG.Monster.Griess
