module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515f.Basic

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515g

variable {Γ : Type*} [Group Γ]

theorem mem_normalizer_inSubgroup_generalizedFitting {C : Subgroup Γ} {x : Γ}
    (hx : x ∈ Subgroup.normalizer (C : Set Γ)) :
    x ∈ Subgroup.normalizer
      ((CFSG.inSubgroup CFSG.generalizedFitting C : Subgroup Γ) : Set Γ) := by
  have key : ∀ x ∈ Subgroup.normalizer (C : Set Γ),
      ∀ y ∈ CFSG.inSubgroup CFSG.generalizedFitting C,
        x * y * x⁻¹ ∈ CFSG.inSubgroup CFSG.generalizedFitting C := by
    intro x hx y hy
    let φ : MulAut ↥C := C.normalizerMonoidHom ⟨x, hx⟩
    have hφ : ∀ t : C, ((φ t : C) : Γ) = x * t * x⁻¹ := fun t =>
      Subgroup.normalizerMonoidHom_apply_apply_coe C ⟨x, hx⟩ t
    have hchar : (CFSG.generalizedFitting ↥C).map φ.toMonoidHom = CFSG.generalizedFitting ↥C :=
      Subgroup.characteristic_iff_map_eq.mp CFSG.LocalCores.generalized_fitting_characteristic.1 φ
    obtain ⟨t, ht, rfl⟩ := hy
    refine ⟨φ t, ?_, (hφ t).symm ▸ rfl⟩
    rw [← hchar]
    exact ⟨t, ht, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  exact ⟨fun hy => key x hx y hy, fun hy => by simpa [mul_assoc] using key x⁻¹ (inv_mem hx) _ hy⟩

theorem mem_normalizer_sSup_of_forall {S : Set (Subgroup Γ)} {a : Γ}
    (h : ∀ J ∈ S, a ∈ Subgroup.normalizer (J : Set Γ)) :
    a ∈ Subgroup.normalizer ((sSup S : Subgroup Γ) : Set Γ) := by
  refine mem_normalizer_sSup (fun J hJ => ?_) (fun J hJ => ?_)
  · rw [map_conj_eq_of_mem_normalizer (h J hJ)]
    exact hJ
  · rw [map_conj_eq_of_mem_normalizer (inv_mem (h J hJ))]
    exact hJ

theorem mem_lcal_of_isSubnormal {X Y J : Subgroup Γ} (hJ : J ∈ lcal Y) (hYX : Y ≤ X)
    (hY : (Y.subgroupOf X).IsSubnormal) : J ∈ lcal X := by
  obtain ⟨hJY, hsub, hs, hnc⟩ := mem_lcal_iff.mp hJ
  exact mem_lcal_iff.mpr ⟨hJY.trans hYX, T515f.isSubnormal_subgroupOf_trans hJY hYX hsub hY, hs,
    hnc⟩

theorem sol_le_sol_of_le_normalizer [Finite Γ] {X Y : Subgroup Γ} (hXY : X ≤ Y)
    (hY : Y ≤ Subgroup.normalizer (X : Set Γ)) : sol X ≤ sol Y := by
  have hsX : sol X ≤ Y := (sol_le X).trans hXY
  have := isSolvable_sol X
  have hn : ((sol X).subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hsX).mpr
      (hY.trans (SolQuot.normalizer_le_nrm_sol X))
  have hs : Group.IsSolvable ((sol X).subgroupOf Y) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hsX).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hsX).injective
  have hle := Nonsolvable.le_solvableRadical hn hs
  rw [← subgroupOf_sol Y] at hle
  exact CFSG.LocalCores.le_of_subgroupOf_le hsX hle

theorem le_centralizer_of_le [Finite Γ] {p : ℕ} {A B G : Subgroup Γ} (h : KSetting p A G)
    (hBA : B ≤ A) : A ≤ Subgroup.centralizer (B : Set Γ) := fun a ha => by
  have := h.elemAbelian.1
  exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
    congrArg Subtype.val (mul_comm' (⟨b, hBA hb⟩ : A) ⟨a, ha⟩)

theorem le_normalizer_inf_centralizer [Finite Γ] {p : ℕ} {A B G : Subgroup Γ} (h : KSetting p A G)
    (hBA : B ≤ A) :
    A ≤ Subgroup.normalizer ((G ⊓ Subgroup.centralizer (B : Set Γ) : Subgroup Γ) : Set Γ) :=
  fun _ ha => mem_normalizer_inf (h.normalizes ha)
    (Subgroup.le_normalizer (le_centralizer_of_le h hBA ha))

theorem inf_centralizer_le_inf_centralizer {A B : Subgroup Γ} (G : Subgroup Γ) (hBA : B ≤ A) :
    G ⊓ Subgroup.centralizer (A : Set Γ) ≤ G ⊓ Subgroup.centralizer (B : Set Γ) :=
  inf_le_inf_left G (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBA))

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.T515g
