module

public import CFSG.LieType.Chevalley.C2E6StdMatrixModel
public import CFSG.Monster.Existence.StdOdd.Defs
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie
public meta import Certificates.Data.CFSGNative.Chevalley.C2E6StdMatrix
public meta import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie
public meta import CFSG.LieType.Chevalley.C2E6StdMatrixData
public meta import CFSG.Monster.B.Classical.E6AdjointTable
public import CFSG.Monster.B.Classical.E6AdjointGroup
import Certificates.Kernel.Misc.E6StdSlp
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate1953
public import Certificates.Certificate1954
public import CFSG.LieType.Chevalley.C2E6StdMatrixData
public import CFSG.Monster.GMS.Facts.TableV

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint
  CFSG.Monster.Existence.StdOdd

abbrev Pt : Type := Fin 78 → K

@[expose] noncomputable def ofPt :
    Pt ≃ₗ[K] RootModule Tag.E6 K := labBasis.equivFun.symm

theorem ofPt_apply
    (u : Pt) : ofPt u = ∑ k, u k • Finsupp.single (lab k) 1 := by
  simp [ofPt, Module.Basis.equivFun_symm_apply, labBasis_apply]

theorem ofPt_repr
    (x : RootModule Tag.E6 K) : ofPt ⇑(labBasis.repr x) = x := by
  have := labBasis.equivFun.symm_apply_apply x
  rwa [Module.Basis.equivFun_apply] at this

noncomputable instance :
    DistribMulAction Rgrp Pt where
  smul g v := (glMat g.1).mulVec v
  one_smul v := by
    show (glMat (1 : Rgrp).1).mulVec v = v
    simp
  mul_smul g h v := by
    show (glMat (g * h).1).mulVec v = (glMat g.1).mulVec ((glMat h.1).mulVec v)
    simp [Matrix.mulVec_mulVec]
  smul_zero g := Matrix.mulVec_zero _
  smul_add g u w := Matrix.mulVec_add _ _ _

theorem smul_def
    (g : Rgrp) (v : Pt) : g • v = (glMat g.1).mulVec v := rfl

theorem ofPt_smul
    (g : Rgrp) (v : Pt) : ofPt (g • v) = g.1.val (ofPt v) := by
  have h : g • v = ⇑(labBasis.repr (g.1.val (ofPt v))) := by
    funext k
    rw [smul_def, labBasis_repr, ofPt_apply, map_sum]
    simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      Matrix.mulVec, dotProduct, glMat_apply, matOf_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [h, ofPt_repr]

theorem stdGroup_le_adjointGroup :
    stdGroup ≤ adjointGroup Tag.E6 K :=
  (CFSG.LieType.Chevalley.graphFixedRootGroup_le _ _ _).trans
    (CFSG.LieType.Chevalley.twistedFixedGroup_le_adjointGroup _ _ _)

@[expose] noncomputable def formPt
    (u w : Pt) : K := form K (ofPt u) (ofPt w)

@[expose] noncomputable def brPt
    (u w : Pt) : Pt := ofPt.symm (bracket K (ofPt u) (ofPt w))

theorem ofPt_brPt
    (u w : Pt) : ofPt (brPt u w) = bracket K (ofPt u) (ofPt w) :=
  ofPt.apply_symm_apply _

theorem formPt_smul
    (g : Rgrp) (u w : Pt) : formPt (g • u) (g • w) = formPt u w := by
  unfold formPt
  rw [ofPt_smul, ofPt_smul]
  exact adjointGroup_form (stdGroup_le_adjointGroup g.2) _ _

theorem brPt_smul
    (g : Rgrp) (u w : Pt) : brPt (g • u) (g • w) = g • brPt u w := by
  apply ofPt.injective
  rw [ofPt_brPt, ofPt_smul, ofPt_smul, ofPt_smul, ofPt_brPt]
  exact (adjointGroup_bracket (stdGroup_le_adjointGroup g.2) _ _).symm

@[expose] def e7 : Pt := Pi.single 7 1

@[expose] def rootOrbit :
    Set Pt := MulAction.orbit Rgrp e7

theorem smul_mem_rootOrbit_iff
    (g : Rgrp) (x : Pt) : g • x ∈ rootOrbit ↔ x ∈ rootOrbit := by
  simp only [rootOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨h, hx⟩
    refine ⟨g⁻¹ * h, ?_⟩
    rw [mul_smul, hx, inv_smul_smul]
  · rintro ⟨h, rfl⟩
    exact ⟨g * h, mul_smul g h e7⟩

theorem formPt_eq (u w : Pt) :
    formPt u w = ∑ a : Fin 78, ∑ b : Fin 78, if fbit a b then u a * w b else 0 := by
  unfold formPt
  rw [ofPt_apply u]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ofPt_apply w]
  simp only [map_sum, map_smul, smul_eq_mul, form_lab, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

@[expose] def maskPt (m : ℕ) : Pt := fun k => if m.testBit k then 1 else 0

theorem toVec_eq_ofPt (m : ℕ) : toVec K m = ofPt (maskPt m) := by
  rw [ofPt_apply, toVec]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : m.testBit k <;> simp [maskPt, h]

theorem brPt_eq (u w : Pt) :
    brPt u w = ∑ a : Fin 78, ∑ b : Fin 78, (u a * w b) • maskPt (brMask a b) := by
  apply ofPt.injective
  rw [ofPt_brPt, ofPt_apply u]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ofPt_apply w]
  simp only [map_sum, map_smul, bracket_lab, toVec_eq_ofPt, Finset.smul_sum, smul_smul]

open CFSG.Monster.Existence.StdOdd.CertNative

end CFSG.Monster.Existence.StdOdd.Cert
