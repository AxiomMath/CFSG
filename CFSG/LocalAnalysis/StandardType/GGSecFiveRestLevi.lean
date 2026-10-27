module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeALevi

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.Universal CFSG.LieType.RootSystem SpecialLinear

variable {n : ℕ} {F : Type} [Field F]

variable (n F) in
@[expose] noncomputable def slBlockHom₂ :
    Matrix.SpecialLinearGroup (Fin (n + 1)) F →*
      Matrix.SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F :=
  (slBlockHom (n + 1) F).comp (slBlockHom n F)

theorem slBlockHom₂_apply (g : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
    slBlockHom₂ n F g = slBlockHom (n + 1) F (slBlockHom n F g) := rfl

theorem slBlockHom₂_injective : Function.Injective (slBlockHom₂ n F) :=
  slBlockHom_injective.comp slBlockHom_injective

theorem slBlockHom₂_transvection {i j : Fin (n + 1)} (hij : i ≠ j) (c : F) :
    slBlockHom₂ n F (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection
        ((Fin.castSucc_injective _).ne ((Fin.castSucc_injective _).ne hij)) c := by
  rw [slBlockHom₂_apply, slBlockHom_transvection, slBlockHom_transvection]

theorem slBlockHom₂_weylRep (j : Fin n) :
    slBlockHom₂ n F (weylRep n F j) = weylRep (n + 1 + 1) F j.castSucc.castSucc := by
  rw [slBlockHom₂_apply, slBlockHom_weylRep, slBlockHom_weylRep]

theorem castSucc_castSucc_mem_typeALeviJ (k : Fin n) :
    (k.castSucc.castSucc : Fin (n + 1 + 1)) ∈ typeALeviJ (n + 1 + 1) (n + 1) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩

theorem range_slBlockHom₂ : (slBlockHom₂ n F).range =
    ggSub (rootDatum (n + 1 + 1) F)
      (ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1))) := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← iSup_fundamentalRootSubgroup_eq_top (m := n) (F := F),
      Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    have hk := castSucc_castSucc_mem_typeALeviJ k
    have e1 : ((k.castSucc.castSucc : Fin (n + 1 + 1))).castSucc =
        (k.castSucc.castSucc.castSucc : Fin (n + 1 + 1 + 1)) := rfl
    have e2 : ((k.castSucc.castSucc : Fin (n + 1 + 1))).succ =
        (k.succ.castSucc.castSucc : Fin (n + 1 + 1 + 1)) := by
      rw [Fin.succ_castSucc, Fin.succ_castSucc]
    have hne : ((k.castSucc.castSucc : Fin (n + 1 + 1))).castSucc ≠
        ((k.castSucc.castSucc : Fin (n + 1 + 1))).succ := Fin.castSucc_lt_succ.ne
    rintro _ ⟨z, hz, rfl⟩
    cases s
    · obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ z).mp hz
      rw [slBlockHom₂_transvection]
      refine rootGroup_le_ggSub (neg_single_mem_ggSupp hk) ?_
      rw [transvection_eq_of_eq _ hne.symm e2.symm e1.symm c]
      exact transvection_mem_rootGroup_neg_single _ hne.symm c
    · obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ z).mp hz
      rw [slBlockHom₂_transvection]
      refine rootGroup_le_ggSub (single_mem_ggSupp hk) ?_
      rw [transvection_eq_of_eq _ hne e1.symm e2.symm c]
      exact transvection_mem_rootGroup_single _ hne c
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨a, b, hab, ha, hb, hγab⟩ := typeALevi_root_of_mem (n + 1 + 1) F hγ
    change rootGroup (n + 1 + 1) F γ ≤ _
    rw [rootGroup_eq (n + 1 + 1) F hab hγab]
    intro z hz
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup hab z).mp hz
    let a' : Fin (n + 1) := ⟨a.val, ha⟩
    let b' : Fin (n + 1) := ⟨b.val, hb⟩
    have ea : a'.castSucc.castSucc = a := Fin.ext rfl
    have eb : b'.castSucc.castSucc = b := Fin.ext rfl
    have hab' : a' ≠ b' := fun h => hab (by rw [← ea, ← eb, h])
    refine ⟨SpecialLinearGroup.transvection hab' c, ?_⟩
    rw [slBlockHom₂_transvection]

theorem slBlockHom₂_mem (g : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
    slBlockHom₂ n F g ∈ ggSub (rootDatum (n + 1 + 1) F)
      (ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1))) := by
  rw [← range_slBlockHom₂]
  exact ⟨g, rfl⟩

theorem exists_slBlockHom₂_eq {u : Matrix.SpecialLinearGroup (Fin (n + 1 + 1 + 1)) F}
    (hu : u ∈ ggSub (rootDatum (n + 1 + 1) F)
      (ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1)))) :
    ∃ g, slBlockHom₂ n F g = u := by
  rw [← range_slBlockHom₂] at hu
  exact hu

section Hom

variable {X : Type*} [Group X]

@[expose] noncomputable def typeALeviHom₂ (φ₁ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* X) :
    ggSub (rootDatum (n + 1 + 1) F)
      (ggSupp (rootDatum (n + 1 + 1) F) (typeALeviJ (n + 1 + 1) (n + 1))) →* X :=
  φ₁.comp ((MonoidHom.ofInjective (slBlockHom₂_injective (n := n) (F := F))).symm.toMonoidHom.comp
    (MulEquiv.subgroupCongr (range_slBlockHom₂ (n := n) (F := F))).symm.toMonoidHom)

theorem typeALeviHom₂_apply (φ₁ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* X)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
    typeALeviHom₂ φ₁ ⟨slBlockHom₂ n F g, slBlockHom₂_mem g⟩ = φ₁ g := by
  have h1 : (MulEquiv.subgroupCongr (range_slBlockHom₂ (n := n) (F := F))).symm
      ⟨slBlockHom₂ n F g, slBlockHom₂_mem g⟩ = MonoidHom.ofInjective slBlockHom₂_injective g :=
    Subtype.ext (by rw [MonoidHom.ofInjective_apply]; rfl)
  change φ₁ ((MonoidHom.ofInjective (slBlockHom₂_injective (n := n) (F := F))).symm
    ((MulEquiv.subgroupCongr (range_slBlockHom₂ (n := n) (F := F))).symm
      ⟨slBlockHom₂ n F g, slBlockHom₂_mem g⟩)) = φ₁ g
  rw [h1, MulEquiv.symm_apply_apply]

theorem ggExt_typeALeviHom₂ (φ₁ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* X)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) F) :
    ggExt (typeALeviHom₂ φ₁) (slBlockHom₂ n F g) = φ₁ g := by
  rw [ggExt_of_mem _ (slBlockHom₂_mem g), typeALeviHom₂_apply]

theorem range_typeALeviHom₂ (φ₁ : Matrix.SpecialLinearGroup (Fin (n + 1)) F →* X) :
    (typeALeviHom₂ φ₁).range = φ₁.range := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    obtain ⟨g, hg⟩ := exists_slBlockHom₂_eq u.2
    have e : u = ⟨slBlockHom₂ n F g, slBlockHom₂_mem g⟩ := Subtype.ext hg.symm
    rw [e, typeALeviHom₂_apply]
    exact ⟨g, rfl⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, typeALeviHom₂_apply φ₁ g⟩

end Hom

end CFSG.StandardType
