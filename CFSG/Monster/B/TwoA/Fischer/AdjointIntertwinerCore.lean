module

public import CFSG.Monster.B.TwoA.Fischer.GramData
public import CFSG.Monster.B.TwoA.Fischer.Slice
public import CFSG.Monster.B.E6.FixedE6RootVector
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
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
  CFSG.Monster.B.Classical.E6Adjoint
open CFSG.LieType.Chevalley.C2E6Overlap (K)

local notation "VE6" => CFSG.Monster.B.E6.FixedE6.V

@[expose] def bracketBil : fixedL →ₗ[ZMod 2] fixedL →ₗ[ZMod 2] fixedL :=
  LinearMap.mk₂ (ZMod 2) bracketL
    (fun u u' v => Subtype.ext (by
      change bracket K ((u : VE6) + u') v = bracket K u v + bracket K u' v
      rw [map_add, LinearMap.add_apply]))
    (fun c u v => Subtype.ext (by
      change bracket K (c • (u : VE6)) v = c • bracket K u v
      rw [← algebraMap_smul K c (u : VE6), map_smul, LinearMap.smul_apply,
        algebraMap_smul]))
    (fun u v v' => Subtype.ext (map_add (bracket K (u : VE6)) (v : VE6) v'))
    (fun c u v => Subtype.ext (by
      change bracket K (u : VE6) (c • (v : VE6)) = c • bracket K u v
      rw [← algebraMap_smul K c (v : VE6), map_smul, algebraMap_smul]))

theorem bracketBil_apply (u v : fixedL) : bracketBil u v = bracketL u v := rfl

theorem bracketL_self'
    (u : fixedL) : bracketL u u = 0 := Subtype.ext (bracket_self _)

theorem bracketL_jacobi
    (u v w : fixedL) :
    bracketL u (bracketL v w) + bracketL v (bracketL w u) + bracketL w (bracketL u v) = 0 := by
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_add, Submodule.coe_zero]
  exact bracket_jacobi (u : VE6) v w

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

section Def

variable (ρ : sliceGroup lab Y →* stdGroup)

@[expose] def adjVec
    (y : Y) : fixedL := rootVecOf (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)

@[expose] def adjMap :
    (Y →₀ ZMod 2) →ₗ[ZMod 2] fixedL :=
  Finsupp.linearCombination (ZMod 2) (adjVec ρ)

theorem adjMap_single
    (y : Y) (c : ZMod 2) : adjMap ρ (Finsupp.single y c) = c • adjVec ρ y :=
  Finsupp.linearCombination_single _ _ _

theorem adjMap_single_one
    (y : Y) : adjMap ρ (Finsupp.single y 1) = adjVec ρ y := by
  rw [adjMap_single, one_smul]

end Def

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y) {ρ : sliceGroup lab Y →* stdGroup}
  (hρ : Function.Injective ρ) (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
include hS hρ hroot

omit hS hroot in
theorem commute_rho_iff (y z : Y) :
    Commute (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩) (ρ ⟨lab z, lab_mem_sliceGroup z.2⟩) ↔
      Commute (lab y) (lab z) := by
  constructor
  · intro h
    have h' : (⟨lab y, lab_mem_sliceGroup y.2⟩ * ⟨lab z, lab_mem_sliceGroup z.2⟩ :
        sliceGroup lab Y) = ⟨lab z, lab_mem_sliceGroup z.2⟩ * ⟨lab y, lab_mem_sliceGroup y.2⟩ :=
      hρ (by rw [map_mul, map_mul]; exact h.eq)
    exact congrArg Subtype.val h'
  · intro h
    have h' : Commute (⟨lab y, lab_mem_sliceGroup y.2⟩ : sliceGroup lab Y)
        ⟨lab z, lab_mem_sliceGroup z.2⟩ := Subtype.ext h.eq
    exact h'.map ρ

omit hroot in
theorem orderOf_rho_mul {y z : Y} (h : ¬Commute (lab y) (lab z)) :
    orderOf (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ * ρ ⟨lab z, lab_mem_sliceGroup z.2⟩) = 3 := by
  rw [← map_mul, orderOf_injective ρ hρ, ← Subgroup.orderOf_coe]
  exact hS.orderOf_mul y y.2 z z.2 h

theorem formL_adjVec
    (y z : Y) : formL (adjVec ρ y) (adjVec ρ z) = ncommInd lab y z := by
  by_cases hc : Commute (lab y) (lab z)
  · rw [ncommInd_of_commute lab hc]
    exact (formL_bracketL_of_commute (hroot y) (hroot z) ((commute_rho_iff hρ y z).2 hc)).1
  · rw [ncommInd_of_not_commute lab hc]
    exact (formL_bracketL_of_orderOf_eq_three (hroot y) (hroot z)
      (hS.orderOf_rho_mul hρ hc)).1

theorem formL_adjMap
    (u u' : Y →₀ ZMod 2) :
    formL (adjMap ρ u) (adjMap ρ u') = ncommForm lab Y u u' := by
  have key : formL.compl₁₂ (adjMap ρ) (adjMap ρ) = ncommForm lab Y :=
    Finsupp.lhom_ext fun y a => Finsupp.lhom_ext fun z b => by
      rw [LinearMap.compl₁₂_apply, adjMap_single, adjMap_single, map_smul, map_smul,
        LinearMap.smul_apply, hS.formL_adjVec hρ hroot, ncommForm_single, smul_eq_mul,
        smul_eq_mul]
      ring
  exact LinearMap.congr_fun₂ key u u'

omit hρ hroot in
theorem rho_conj_lab (y z : Y) (hyz : act (lab y) z ∈ Y) :
    ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ * ρ ⟨lab z, lab_mem_sliceGroup z.2⟩ *
        ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ =
      ρ ⟨lab (act (lab y) z), lab_mem_sliceGroup hyz⟩ := by
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change lab y * lab z * lab y = lab (act (lab y) z)
  have hy2 : (lab y)⁻¹ = lab y := by
    have h := hS.orderOf_lab y y.2
    rw [inv_eq_iff_mul_eq_one, ← sq, ← h, pow_orderOf_eq_one]
  rw [hS.lab_act, hy2]

theorem bracketL_adjVec (y z : Y) :
    bracketL (adjVec ρ y) (adjVec ρ z) =
      adjMap ρ (ncommProd act lab Y (Finsupp.single y 1) (Finsupp.single z 1)) := by
  by_cases hc : Commute (lab y) (lab z)
  · rw [ncommProd_single_of_commute act lab Y hc, map_zero]
    exact (formL_bracketL_of_commute (hroot y) (hroot z) ((commute_rho_iff hρ y z).2 hc)).2
  · have hyz : act (lab y) z ∈ Y := hS.mapsTo _ (lab_mem_sliceGroup y.2) z z.2
    rw [ncommProd_single_of_not_commute act lab Y hc hyz, map_add, map_add, adjMap_single_one,
      adjMap_single_one, adjMap_single_one]
    refine (formL_bracketL_of_orderOf_eq_three (hroot y) (hroot z)
      (hS.orderOf_rho_mul hρ hc)).2.trans ?_
    rw [hS.rho_conj_lab y z hyz]
    rfl

theorem adjMap_ncommProd
    (u u' : Y →₀ ZMod 2) :
    adjMap ρ (ncommProd act lab Y u u') = bracketL (adjMap ρ u) (adjMap ρ u') := by
  have key : (ncommProd act lab Y).compr₂ (adjMap ρ) = bracketBil.compl₁₂ (adjMap ρ) (adjMap ρ) :=
    Finsupp.lhom_ext fun y a => Finsupp.lhom_ext fun z b => by
      rw [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, ← Finsupp.smul_single_one y a,
        ← Finsupp.smul_single_one z b]
      simp only [map_smul, LinearMap.smul_apply, adjMap_single_one, bracketBil_apply]
      rw [hS.bracketL_adjVec hρ hroot]
  exact LinearMap.congr_fun₂ key u u'

omit hρ in
theorem adjVec_act
    (h : sliceGroup lab Y) (y : Y) (hy : act (h : S) y ∈ Y) :
    adjVec ρ ⟨act (h : S) y, hy⟩ = gL (ρ h) (adjVec ρ y) := by
  have hq : SemidirectProduct.inl (ρ ⟨lab (act (h : S) y), lab_mem_sliceGroup hy⟩) =
      SemidirectProduct.inl (ρ h) * SemidirectProduct.inl (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩) *
        (SemidirectProduct.inl (ρ h) : GStar)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (hS.lab_act _ _)
  rw [adjVec, (rootVecOf_conj_star _ (hroot y) hq).2, actStar_inl_eq_gL]
  rfl

omit hρ in
theorem adjMap_ncommRep
    (h : sliceGroup lab Y) (u : Y →₀ ZMod 2) :
    adjMap ρ (ncommRep act Y (sliceGroup lab Y) hS.mapsTo h u) = gL (ρ h) (adjMap ρ u) := by
  have key : (adjMap ρ).comp (ncommRep act Y (sliceGroup lab Y) hS.mapsTo h) =
      (gL (ρ h)).comp (adjMap ρ) :=
    Finsupp.lhom_ext fun y a => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ncommRep_single, adjMap_single,
        adjMap_single, map_smul]
      congr 1
      exact hS.adjVec_act hroot h y _
  exact LinearMap.congr_fun key u

theorem ker_adjMap
    (hsurj : Function.Surjective (adjMap ρ)) :
    LinearMap.ker (adjMap ρ) = ncommRad lab Y := by
  ext u
  rw [LinearMap.mem_ker, mem_ncommRad_iff]
  constructor
  · intro h w
    rw [← hS.formL_adjMap hρ hroot, h, map_zero, LinearMap.zero_apply]
  · intro h
    refine formL_nondegenerate.1 _ fun v => ?_
    obtain ⟨w, rfl⟩ := hsurj v
    rw [hS.formL_adjMap hρ hroot]
    exact h w

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
