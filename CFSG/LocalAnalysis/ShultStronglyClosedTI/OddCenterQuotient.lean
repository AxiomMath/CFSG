module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralLiftStructure

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open

variable (E : Type*) [Group E]

@[expose] def oddCenterSubgroup : Subgroup E :=
  (CFSG.pPrimeCore 2 (Subgroup.center E)).map (Subgroup.center E).subtype

theorem oddCenterSubgroup_le_center : oddCenterSubgroup E ≤ Subgroup.center E :=
  Subgroup.map_subtype_le _

instance oddCenterSubgroup_characteristic : (oddCenterSubgroup E).Characteristic := by
  unfold oddCenterSubgroup
  infer_instance

instance oddCenterSubgroup_normal : (oddCenterSubgroup E).Normal :=
  Subgroup.normal_of_le_center (oddCenterSubgroup_le_center E)

variable [Finite E]

theorem oddCenterSubgroup_odd_card : Odd (Nat.card (oddCenterSubgroup E)) := by
  rw [oddCenterSubgroup, Subgroup.card_subtype]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2))

omit [Finite E] in
theorem oddCenterSubgroup_maximal (B : Subgroup E)
    (hB : B ≤ Subgroup.center E) (hodd : Odd (Nat.card B)) :
    B ≤ oddCenterSubgroup E := by
  have hlocal : B.subgroupOf (Subgroup.center E) ≤
      CFSG.pPrimeCore 2 (Subgroup.center E) := by
    apply le_sSup
    refine ⟨Subgroup.normal_of_isMulCommutative _, ?_⟩
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv]
    exact hodd.coprime_two_left
  intro b hb
  exact Subgroup.mem_map.mpr ⟨⟨b, hB hb⟩, hlocal hb, rfl⟩

theorem oddCenterSubgroup_center_image_isPGroup :
    IsPGroup 2 ((Subgroup.center E).map (QuotientGroup.mk' (oddCenterSubgroup E))) := by
  let Z := Subgroup.center E
  let O := CFSG.pPrimeCore 2 Z
  let A := oddCenterSubgroup E
  let q := QuotientGroup.mk' A
  let f := q.subgroupMap Z
  have htop : (⊤ : Subgroup Z) ≤ CFSG.pCore 2 Z ⊔ O :=
    CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (inferInstance : Group.IsNilpotent Z)
  apply (CFSG.pCore_isPGroup (p := 2) (G := Z)).of_surjective
    (f.comp (CFSG.pCore 2 Z).subtype)
  intro y
  obtain ⟨z, rfl⟩ := q.subgroupMap_surjective Z y
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Subgroup.mem_sup_of_normal_right.mp (htop (Subgroup.mem_top z))
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  change q (a : E) = q (z : E)
  have hbA : (b : E) ∈ A := Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
  have hbq : q (b : E) = 1 := (QuotientGroup.eq_one_iff (b : E)).mpr hbA
  have hz : (z : E) = (a : E) * b := congrArg Subtype.val hab.symm
  rw [hz, map_mul, hbq, mul_one]

variable [Group.IsPerfect E]

omit [Finite E] in
theorem oddCenterSubgroup_center_image :
    (Subgroup.center E).map (QuotientGroup.mk' (oddCenterSubgroup E)) =
      Subgroup.center (E ⧸ oddCenterSubgroup E) :=
  CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
    (QuotientGroup.mk' (oddCenterSubgroup E)) (QuotientGroup.mk'_surjective _)
    (by simpa only [QuotientGroup.ker_mk'] using oddCenterSubgroup_le_center E)

omit [Finite E] in
theorem oddCenterSubgroup_center_preimage :
    (Subgroup.center (E ⧸ oddCenterSubgroup E)).comap
      (QuotientGroup.mk' (oddCenterSubgroup E)) = Subgroup.center E :=
  CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel
    (QuotientGroup.mk' (oddCenterSubgroup E)) (QuotientGroup.mk'_surjective _)
    (by simpa only [QuotientGroup.ker_mk'] using oddCenterSubgroup_le_center E)

theorem oddCenterSubgroup_quotient_center_isPGroup :
    IsPGroup 2 (Subgroup.center (E ⧸ oddCenterSubgroup E)) := by
  rw [← oddCenterSubgroup_center_image E]
  exact oddCenterSubgroup_center_image_isPGroup E

@[expose] def oddCenterQuotientCenterEquiv :
    (E ⧸ Subgroup.center E) ≃*
      ((E ⧸ oddCenterSubgroup E) ⧸ Subgroup.center (E ⧸ oddCenterSubgroup E)) :=
  centralLiftCenterQuotientEquiv (QuotientGroup.mk' (oddCenterSubgroup E))
    (QuotientGroup.mk'_surjective _)
    (by simpa only [QuotientGroup.ker_mk'] using oddCenterSubgroup_le_center E)

theorem odd_center_quotient_structure (hquasi : IsQuasisimple E)
    (hmodel : fusionIsBenderGroup (E ⧸ Subgroup.center E)) :
    IsQuasisimple (E ⧸ oddCenterSubgroup E) ∧
      Group.IsPerfect (E ⧸ oddCenterSubgroup E) ∧
      IsPGroup 2 (Subgroup.center (E ⧸ oddCenterSubgroup E)) ∧
      fusionIsBenderGroup
        ((E ⧸ oddCenterSubgroup E) ⧸ Subgroup.center (E ⧸ oddCenterSubgroup E)) := by
  refine ⟨CFSG.ComponentClassification.Quasisimple.central_quotient hquasi
    (oddCenterSubgroup E) (oddCenterSubgroup_le_center E), inferInstance,
    oddCenterSubgroup_quotient_center_isPGroup E, ?_⟩
  exact central_lift_model_transport (oddCenterQuotientCenterEquiv E).symm hmodel

end CFSG.ShultStronglyClosedTI
