module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart29
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PinnedBaseChange

@[expose] public section

public noncomputable section

variable {E : Type} [Field E] [CharP E 2] [Finite E]

namespace CFSG.StandardType.F4ExplicitPos.B2Finite

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed
  CFSG.SeitzReduction.F4Pilot

open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed spEmbed_injective)

open C3Range (c3RootSubgroup c3RootSubgroup_eq_rootGroup f4C3_exists_pinned_full)

open CFSG.StandardType.F4ExplicitPos.FiniteAction (rootSpanOver)

open CFSG.StandardType.F4ExplicitPos.PinnedBaseChange (bcGL_pinnedX)

open CFSG.StandardType.F4ExplicitPos.BaseChange (bcGL bcGL_injective)

noncomputable def c3Iota :
    ↥(StatedSp 3 E) →* ↥(adjointGroup .F4 E) :=
  (f4C3_exists_pinned_full (K := E)).choose

theorem c3Iota_injective :
    Function.Injective (c3Iota (E := E)) :=
  (f4C3_exists_pinned_full (K := E)).choose_spec.1

theorem c3Iota_rootSubgroup
    {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    (c3RootSubgroup (K := E) γ).map ((adjointGroup .F4 E).subtype.comp c3Iota) =
      CFSG.Blueprint.Chevalley.rootSubgroup .F4 E (c3ToF4 γ) :=
  (f4C3_exists_pinned_full (K := E)).choose_spec.2.2.2 hγ

noncomputable def b2LeviHom :
    ↥(StatedSp 2 E) →* ↥(adjointGroup .F4 E) :=
  (c3Iota (E := E)).comp (spEmbed (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2))

theorem b2LeviHom_injective :
    Function.Injective (b2LeviHom (E := E)) :=
  (c3Iota_injective (E := E)).comp (spEmbed_injective (Fin.succ_injective 2))

theorem map_b2LeviHom_rootGroup_modGL
    {v : Fin 2 → ℤ} (hv : v ∈ roots (isFiniteType_cartanC 2) ∅) :
    ((Symplectic.rootGroup 2 E v).map (b2LeviHom (E := E))).map (adjointGroup .F4 E).subtype =
      CFSG.Blueprint.Chevalley.rootSubgroup .F4 E (c2ToF4 v) := by
  have hcomp : (adjointGroup .F4 E).subtype.comp (b2LeviHom (E := E))
      = ((adjointGroup .F4 E).subtype.comp c3Iota).comp
          (spEmbed (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2)) := rfl
  have hroot : Symplectic.rootGroup 3 E (shiftC2 v)
      = c3RootSubgroup (K := E) (shiftC2 v) :=
    (c3RootSubgroup_eq_rootGroup (K := E) (shiftC2_mem_roots hv)).symm
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_spEmbed_rootGroup hv, hroot,
    c3Iota_rootSubgroup (shiftC2_mem_roots hv), c2ToF4_apply]

theorem map_range_b2LeviHom_modGL :
    ((b2LeviHom (E := E)).range).map (adjointGroup .F4 E).subtype
      = rootSpan .F4 E b2LeviRoots := by
  have hgen : ((b2LeviHom (E := E)).range).map (adjointGroup .F4 E).subtype
      = ⨆ v ∈ roots (isFiniteType_cartanC 2) ∅,
          ((Symplectic.rootGroup 2 E v).map (b2LeviHom (E := E))).map
            (adjointGroup .F4 E).subtype := by
    rw [MonoidHom.range_eq_map, Subgroup.map_map,
      ← (Symplectic.isCTGroupDatum 2 E).iSup_eq_top]
    simp only [Subgroup.map_iSup, Subgroup.map_map]
  rw [hgen, rootSpan]
  refine le_antisymm (iSup₂_le fun v hv => ?_) (iSup₂_le fun γ hγ => ?_)
  · rw [map_b2LeviHom_rootGroup_modGL hv]
    exact le_iSup₂ (f := fun γ (_ : γ ∈ b2LeviRoots) =>
      CFSG.Blueprint.Chevalley.rootSubgroup .F4 E γ) _ (c2ToF4_mem_b2LeviRoots hv)
  · obtain ⟨v, hv, rfl⟩ := exists_c2ToF4_eq_of_mem_b2LeviRoots hγ
    rw [← map_b2LeviHom_rootGroup_modGL hv]
    exact le_iSup₂ (f := fun v (_ : v ∈ roots (isFiniteType_cartanC 2) ∅) =>
      ((Symplectic.rootGroup 2 E v).map (b2LeviHom (E := E))).map
        (adjointGroup .F4 E).subtype) v hv

theorem rootSpanOver_eq_map_rootSpan
    {Ω : Type} [Field Ω] (F : Subfield Ω)
    (Ψ : Set (Fin Tag.F4.rank → ℤ)) :
    rootSpanOver Ω F Ψ = (rootSpan .F4 F Ψ).map (bcGL F.subtype) := by
  refine le_antisymm ?_ ?_
  · rw [rootSpanOver, Subgroup.closure_le]
    rintro x ⟨α, hα, c, rfl⟩
    exact Subgroup.mem_map.2 ⟨pinnedX .F4 F α c, by
      rw [rootSpan]
      exact Subgroup.mem_iSup_of_mem α
        (Subgroup.mem_iSup_of_mem hα (Subgroup.subset_closure ⟨c, rfl⟩)),
      bcGL_pinnedX F.subtype α c⟩
  · rw [rootSpanOver, Subgroup.map_le_iff_le_comap, rootSpan]
    refine iSup_le fun α => iSup_le fun hα => ?_
    rw [← Subgroup.map_le_iff_le_comap, rootSubgroup, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro x ⟨c, hc, rfl⟩
    obtain ⟨d, rfl⟩ := hc
    rw [bcGL_pinnedX]
    exact Subgroup.subset_closure ⟨α, hα, d, rfl⟩

end CFSG.StandardType.F4ExplicitPos.B2Finite

end

end
