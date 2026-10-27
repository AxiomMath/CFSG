module

public import CFSG.LocalAnalysis.StandardType.GGA11Defs

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

@[expose] noncomputable def slBlock84 : SL 8 →* SL 12 := (slBlockHom₃ 8 F2).comp (slBlockHom 7 F2)

theorem slBlock84_injective : Function.Injective slBlock84 :=
  slBlockHom₃_injective.comp slBlockHom_injective

theorem slBlock84_transvection {i j : Fin 8} (hij : i ≠ j) (c : F2) :
    slBlock84 (SpecialLinearGroup.transvection hij c) =
      SpecialLinearGroup.transvection (i := i.castSucc.castSucc.castSucc.castSucc)
        (j := j.castSucc.castSucc.castSucc.castSucc)
        (fun e => hij (Fin.castSucc_injective _ (Fin.castSucc_injective _
          (Fin.castSucc_injective _ (Fin.castSucc_injective _ e))))) c := by
  rw [slBlock84, MonoidHom.comp_apply, slBlockHom_transvection (n := 7) (F := F2),
    slBlockHom₃_apply, slBlockHom₂_transvection (n := 8) (F := F2),
    slBlockHom_transvection (n := 10) (F := F2)]

theorem slBlock84_weylRep (j : Fin 7) :
    slBlock84 (weylRep 7 F2 j) = weylRep 11 F2 j.castSucc.castSucc.castSucc.castSucc := by
  rw [slBlock84, MonoidHom.comp_apply, slBlockHom_weylRep (n := 7) (F := F2),
    slBlockHom₃_apply, slBlockHom₂_weylRep (n := 8) (F := F2),
    slBlockHom_weylRep (n := 10) (F := F2)]

theorem range_slBlock84 : slBlock84.range =
    ggSub (rootDatum 11 F2) (ggSupp (rootDatum 11 F2) (typeALeviJ 11 8)) := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← iSup_fundamentalRootSubgroup_eq_top (m := 7) (F := F2),
      Subgroup.map_iSup]
    refine iSup_le fun k => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun s => ?_
    have hk : (k.castSucc.castSucc.castSucc.castSucc : Fin 11) ∈ typeALeviJ 11 8 := by
      rw [typeALeviJ, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simp only [Fin.val_castSucc]; omega⟩
    have hsucc : (k.succ : Fin 8).castSucc.castSucc.castSucc.castSucc =
        (k.castSucc.castSucc.castSucc.castSucc : Fin 11).succ :=
      Fin.ext (by simp [Fin.val_succ])
    have hne : (k.castSucc.castSucc.castSucc.castSucc : Fin 11).castSucc ≠
        (k.castSucc.castSucc.castSucc.castSucc : Fin 11).succ := Fin.castSucc_lt_succ.ne
    rintro _ ⟨z, hz, rfl⟩
    cases s
    · obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ z).mp hz
      rw [slBlock84_transvection]
      refine rootGroup_le_ggSub (neg_single_mem_ggSupp hk) ?_
      rw [transvection_eq_of_eq _ hne.symm hsucc rfl c]
      exact transvection_mem_rootGroup_neg_single _ hne.symm c
    · obtain ⟨c, rfl⟩ := (mem_rootSubgroup _ z).mp hz
      rw [slBlock84_transvection]
      refine rootGroup_le_ggSub (single_mem_ggSupp hk) ?_
      rw [transvection_eq_of_eq _ hne rfl hsucc c]
      exact transvection_mem_rootGroup_single _ hne c
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨a, b, hab, ha, hb, hγab⟩ := typeALevi_root_of_mem 11 F2 hγ
    change rootGroup 11 F2 γ ≤ _
    rw [rootGroup_eq 11 F2 hab hγab]
    intro z hz
    obtain ⟨c, rfl⟩ := (mem_rootSubgroup hab z).mp hz
    let a' : Fin 8 := ⟨a.val, ha⟩
    let b' : Fin 8 := ⟨b.val, hb⟩
    have ea : a'.castSucc.castSucc.castSucc.castSucc = a := Fin.ext rfl
    have eb : b'.castSucc.castSucc.castSucc.castSucc = b := Fin.ext rfl
    have hab' : a' ≠ b' := fun h => hab (by rw [← ea, ← eb, h])
    refine ⟨SpecialLinearGroup.transvection hab' c, ?_⟩
    rw [slBlock84_transvection]

theorem slBlock84_mem (g : SL 8) :
    slBlock84 g ∈ ggSub (rootDatum 11 F2) (ggSupp (rootDatum 11 F2) (typeALeviJ 11 8)) := by
  rw [← range_slBlock84]
  exact ⟨g, rfl⟩

@[expose] noncomputable def typeALeviHom4 {X : Type*} [Group X] (φ₁ : SL 8 →* X) :
    ggSub (rootDatum 11 F2) (ggSupp (rootDatum 11 F2) (typeALeviJ 11 8)) →* X :=
  φ₁.comp ((MonoidHom.ofInjective slBlock84_injective).symm.toMonoidHom.comp
    (MulEquiv.subgroupCongr range_slBlock84).symm.toMonoidHom)

theorem typeALeviHom4_apply {X : Type*} [Group X] (φ₁ : SL 8 →* X) (g : SL 8) :
    typeALeviHom4 φ₁ ⟨slBlock84 g, slBlock84_mem g⟩ = φ₁ g := by
  have h1 : (MulEquiv.subgroupCongr range_slBlock84).symm
      ⟨slBlock84 g, slBlock84_mem g⟩ = MonoidHom.ofInjective slBlock84_injective g :=
    Subtype.ext (by rw [MonoidHom.ofInjective_apply]; rfl)
  change φ₁ ((MonoidHom.ofInjective slBlock84_injective).symm
    ((MulEquiv.subgroupCongr range_slBlock84).symm
      ⟨slBlock84 g, slBlock84_mem g⟩)) = φ₁ g
  rw [h1, MulEquiv.symm_apply_apply]

theorem ggExt_typeALeviHom4 {X : Type*} [Group X] (φ₁ : SL 8 →* X) (g : SL 8) :
    ggExt (typeALeviHom4 φ₁) (slBlock84 g) = φ₁ g := by
  rw [ggExt_of_mem _ (slBlock84_mem g), typeALeviHom4_apply]

theorem range_typeALeviHom4 {X : Type*} [Group X] (φ₁ : SL 8 →* X) :
    (typeALeviHom4 φ₁).range = φ₁.range := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    have hu : u.val ∈ slBlock84.range := by rw [range_slBlock84]; exact u.2
    obtain ⟨g, hg⟩ := hu
    have e : u = ⟨slBlock84 g, slBlock84_mem g⟩ := Subtype.ext hg.symm
    rw [e, typeALeviHom4_apply]
    exact ⟨g, rfl⟩
  · rintro _ ⟨g, rfl⟩
    exact ⟨_, typeALeviHom4_apply φ₁ g⟩

end CFSG.StandardType.A11

end
