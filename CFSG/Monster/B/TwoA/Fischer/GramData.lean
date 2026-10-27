module

public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import Mathlib.RepresentationTheory.Basic

public noncomputable section

namespace CFSG.Monster.B.TwoA.Fischer

variable {S V : Type*} [Group S] (act : S →* Equiv.Perm V) (lab : V → S) (Y : Set V)

@[expose] def ncommInd (y z : V) : ZMod 2 :=
  open _root_.Classical in if Commute (lab y) (lab z) then 0 else 1

theorem ncommInd_of_commute {y z : V} (h : Commute (lab y) (lab z)) : ncommInd lab y z = 0 :=
  ite_eq_left h

theorem ncommInd_of_not_commute {y z : V} (h : ¬Commute (lab y) (lab z)) :
    ncommInd lab y z = 1 :=
  ite_eq_right h

theorem ncommInd_comm (y z : V) : ncommInd lab y z = ncommInd lab z y := by
  by_cases h : Commute (lab y) (lab z)
  · rw [ncommInd_of_commute lab h, ncommInd_of_commute lab h.symm]
  · rw [ncommInd_of_not_commute lab h, ncommInd_of_not_commute lab fun h' => h h'.symm]

theorem ncommInd_act (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹) (a : S)
    (y z : V) : ncommInd lab (act a y) (act a z) = ncommInd lab y z := by
  have h : Commute (lab (act a y)) (lab (act a z)) ↔ Commute (lab y) (lab z) := by
    rw [hlab, hlab]
    exact Commute.conj_iff a
  by_cases hc : Commute (lab y) (lab z)
  · rw [ncommInd_of_commute lab hc, ncommInd_of_commute lab (h.mpr hc)]
  · rw [ncommInd_of_not_commute lab hc, ncommInd_of_not_commute lab (mt h.mp hc)]

@[expose] def ncommLabels : Set S := lab '' Y

@[expose] def ncommForm : LinearMap.BilinForm (ZMod 2) (Y →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) fun y : Y =>
    Finsupp.linearCombination (ZMod 2) fun z : Y => ncommInd lab y z

theorem ncommForm_single (y z : Y) (a b : ZMod 2) :
    ncommForm lab Y (Finsupp.single y a) (Finsupp.single z b) = a * b * ncommInd lab y z := by
  rw [ncommForm, Finsupp.linearCombination_single, LinearMap.smul_apply,
    Finsupp.linearCombination_single, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem ncommForm_flip : (ncommForm lab Y).flip = ncommForm lab Y :=
  Finsupp.lhom_ext fun y a => Finsupp.lhom_ext fun z b => by
    rw [LinearMap.flip_apply, ncommForm_single, ncommForm_single, ncommInd_comm, mul_comm a b]

theorem ncommForm_comm (u w : Y →₀ ZMod 2) : ncommForm lab Y u w = ncommForm lab Y w u :=
  (LinearMap.flip_apply (ncommForm lab Y) u w).symm.trans
    (LinearMap.congr_fun₂ (ncommForm_flip lab Y) w u)

theorem ncommForm_isSymm : (ncommForm lab Y).IsSymm :=
  LinearMap.isSymm_def.mpr fun u w => ncommForm_comm lab Y u w

@[expose] def ncommRad : Submodule (ZMod 2) (Y →₀ ZMod 2) := LinearMap.ker (ncommForm lab Y)

theorem mem_ncommRad_iff (u : Y →₀ ZMod 2) :
    u ∈ ncommRad lab Y ↔ ∀ w, ncommForm lab Y u w = 0 :=
  LinearMap.mem_ker.trans LinearMap.ext_iff

abbrev NcommQuot : Type _ := (Y →₀ ZMod 2) ⧸ ncommRad lab Y

@[expose] def ncommVec (y : Y) : NcommQuot lab Y := Submodule.Quotient.mk (Finsupp.single y 1)

@[expose] def ncommQuotForm : LinearMap.BilinForm (ZMod 2) (NcommQuot lab Y) :=
  LinearMap.IsRefl.liftQ₂ (ncommForm lab Y) (ncommRad lab Y) (ncommForm_isSymm lab Y).isRefl
    le_rfl

theorem ncommQuotForm_mk (u w : Y →₀ ZMod 2) :
    ncommQuotForm lab Y (Submodule.Quotient.mk u) (Submodule.Quotient.mk w) =
      ncommForm lab Y u w :=
  rfl

theorem ncommQuotForm_ncommVec (y z : Y) :
    ncommQuotForm lab Y (ncommVec lab Y y) (ncommVec lab Y z) = ncommInd lab y z := by
  rw [ncommVec, ncommVec, ncommQuotForm_mk, ncommForm_single, one_mul, one_mul]

theorem ncommQuotForm_comm (x w : NcommQuot lab Y) :
    ncommQuotForm lab Y x w = ncommQuotForm lab Y w x := by
  induction x using Submodule.Quotient.induction_on with | H u => ?_
  induction w using Submodule.Quotient.induction_on with | H w => ?_
  exact ncommForm_comm lab Y u w

theorem ncommQuotForm_nondegenerate : (ncommQuotForm lab Y).Nondegenerate := by
  have hl : LinearMap.SeparatingLeft (ncommQuotForm lab Y) := fun x hx => by
    induction x using Submodule.Quotient.induction_on with | H u => ?_
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      ((mem_ncommRad_iff lab Y u).mpr fun w => hx (Submodule.Quotient.mk w))
  exact ⟨hl, fun x hx => hl x fun w => (ncommQuotForm_comm lab Y x w).trans (hx w)⟩

@[expose] def ncommEps (x : V) : Y →₀ ZMod 2 :=
  open _root_.Classical in if h : x ∈ Y then Finsupp.single ⟨x, h⟩ 1 else 0

theorem ncommEps_of_mem {x : V} (h : x ∈ Y) : ncommEps Y x = Finsupp.single ⟨x, h⟩ 1 :=
  dite_eq_left h

theorem ncommEps_of_notMem {x : V} (h : x ∉ Y) : ncommEps Y x = 0 :=
  dite_eq_right h

@[expose] def ncommProdBasis (y z : Y) : Y →₀ ZMod 2 :=
  open _root_.Classical in
  if Commute (lab y) (lab z) then 0
  else Finsupp.single y 1 + Finsupp.single z 1 + ncommEps Y (act (lab y) z)

@[expose] def ncommProd : (Y →₀ ZMod 2) →ₗ[ZMod 2] (Y →₀ ZMod 2) →ₗ[ZMod 2] (Y →₀ ZMod 2) :=
  Finsupp.linearCombination (ZMod 2) fun y : Y =>
    Finsupp.linearCombination (ZMod 2) fun z : Y => ncommProdBasis act lab Y y z

theorem ncommProd_single (y z : Y) :
    ncommProd act lab Y (Finsupp.single y 1) (Finsupp.single z 1) =
      ncommProdBasis act lab Y y z := by
  rw [ncommProd, Finsupp.linearCombination_single, one_smul, Finsupp.linearCombination_single,
    one_smul]

theorem ncommProd_single_of_commute {y z : Y} (h : Commute (lab y) (lab z)) :
    ncommProd act lab Y (Finsupp.single y 1) (Finsupp.single z 1) = 0 :=
  (ncommProd_single act lab Y y z).trans (ite_eq_left h)

theorem ncommProd_single_of_not_commute {y z : Y} (h : ¬Commute (lab y) (lab z))
    (hyz : act (lab y) z ∈ Y) :
    ncommProd act lab Y (Finsupp.single y 1) (Finsupp.single z 1) =
      Finsupp.single y 1 + Finsupp.single z 1 + Finsupp.single ⟨act (lab y) z, hyz⟩ 1 :=
  (ncommProd_single act lab Y y z).trans
    ((ite_eq_right h).trans (by rw [ncommEps_of_mem Y hyz]))

section Action

variable (H : Subgroup S)

theorem act_mem_iff_of_mapsTo (hH : ∀ h ∈ H, ∀ y ∈ Y, act h y ∈ Y) (h : H) (x : V) :
    act h x ∈ Y ↔ x ∈ Y := by
  refine ⟨fun hx => ?_, hH h h.2 x⟩
  have := hH _ (H.inv_mem h.2) _ hx
  simpa using this

@[expose] def ncommPerm (hH : ∀ h ∈ H, ∀ y ∈ Y, act h y ∈ Y) : H →* Equiv.Perm Y where
  toFun h := (act h).subtypePerm (act_mem_iff_of_mapsTo act Y H hH h)
  map_one' := Equiv.ext fun y => Subtype.ext (by simp)
  map_mul' g h := Equiv.ext fun y => Subtype.ext (by
    show act (g * h : S) y = act g (act h y)
    rw [map_mul]
    rfl)

theorem coe_ncommPerm_apply (hH : ∀ h ∈ H, ∀ y ∈ Y, act h y ∈ Y) (h : H) (y : Y) :
    (ncommPerm act Y H hH h y : V) = act h y :=
  rfl

@[expose] def ncommRep (hH : ∀ h ∈ H, ∀ y ∈ Y, act h y ∈ Y) :
    Representation (ZMod 2) H (Y →₀ ZMod 2) where
  toFun h := Finsupp.lmapDomain (ZMod 2) (ZMod 2) (ncommPerm act Y H hH h)
  map_one' := Finsupp.lhom_ext fun y a => by simp
  map_mul' g h := Finsupp.lhom_ext fun y a => by simp

theorem ncommRep_single (hH : ∀ h ∈ H, ∀ y ∈ Y, act h y ∈ Y) (h : H) (y : Y) (a : ZMod 2) :
    ncommRep act Y H hH h (Finsupp.single y a) = Finsupp.single (ncommPerm act Y H hH h y) a :=
  Finsupp.mapDomain_single

theorem ncommForm_ncommRep (hH : ∀ h ∈ H, ∀ y ∈ Y, act h y ∈ Y)
    (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹) (h : H) (u w : Y →₀ ZMod 2) :
    ncommForm lab Y (ncommRep act Y H hH h u) (ncommRep act Y H hH h w) = ncommForm lab Y u w := by
  have key : (ncommForm lab Y).compl₁₂ (ncommRep act Y H hH h) (ncommRep act Y H hH h) =
      ncommForm lab Y :=
    Finsupp.lhom_ext fun y a => Finsupp.lhom_ext fun z b => by
      rw [LinearMap.compl₁₂_apply, ncommRep_single, ncommRep_single, ncommForm_single,
        ncommForm_single]
      exact congrArg (a * b * ·) (ncommInd_act act lab hlab h y z)
  exact LinearMap.congr_fun₂ key u w

theorem ncommRad_le_comap (hH : ∀ h ∈ H, ∀ y ∈ Y, act h y ∈ Y)
    (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹) (h : H) :
    ncommRad lab Y ≤ (ncommRad lab Y).comap (ncommRep act Y H hH h) := by
  intro u hu
  refine Submodule.mem_comap.mpr ((mem_ncommRad_iff lab Y _).mpr fun w => ?_)
  have hw : ncommRep act Y H hH h (ncommRep act Y H hH h⁻¹ w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [← hw, ncommForm_ncommRep act lab Y H hH hlab]
  exact (mem_ncommRad_iff lab Y u).mp hu _

@[expose] def ncommQuotRep (hH : ∀ h ∈ H, ∀ y ∈ Y, act h y ∈ Y)
    (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹) :
    Representation (ZMod 2) H (NcommQuot lab Y) :=
  (ncommRep act Y H hH).quotient (ncommRad lab Y) (ncommRad_le_comap act lab Y H hH hlab)

theorem ncommQuotRep_mk (hH : ∀ h ∈ H, ∀ y ∈ Y, act h y ∈ Y)
    (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹) (h : H) (u : Y →₀ ZMod 2) :
    ncommQuotRep act lab Y H hH hlab h (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (ncommRep act Y H hH h u) :=
  rfl

theorem ncommQuotRep_ncommVec (hH : ∀ h ∈ H, ∀ y ∈ Y, act h y ∈ Y)
    (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹) (h : H) (y : Y) :
    ncommQuotRep act lab Y H hH hlab h (ncommVec lab Y y) =
      ncommVec lab Y (ncommPerm act Y H hH h y) := by
  rw [ncommVec, ncommQuotRep_mk, ncommRep_single, ncommVec]

end Action

end CFSG.Monster.B.TwoA.Fischer
