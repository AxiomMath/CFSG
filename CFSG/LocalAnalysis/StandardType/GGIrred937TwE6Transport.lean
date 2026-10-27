module

public import CFSG.LieType.Chevalley.GraphFixedCompatibleDiagonal
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure

public section

namespace CFSG.StandardType

namespace Irred937

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Transport

private theorem bcGL937_posUnipotent_le
    {K K' : Type} [Field K] [Field K'] (f : K →+* K') {τ : Tag} :
    (posUnipotent τ K).map (baseChangeGL f) ≤ posUnipotent τ K' := by
  rw [Subgroup.map_le_iff_le_comap]
  conv_lhs => rw [posUnipotent, rootSpan]
  refine iSup_le fun α => iSup_le fun hα => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro g ⟨c, rfl⟩
  exact Subgroup.mem_comap.2 (by
    rw [posUnipotent, rootSpan]
    exact Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem hα
      (Subgroup.subset_closure ⟨f c, (baseChangeGL_pinnedX f α c).symm⟩)))

private theorem bcGL937_negUnipotent_le
    {K K' : Type} [Field K] [Field K'] (f : K →+* K') {τ : Tag} :
    (negUnipotent τ K).map (baseChangeGL f) ≤ negUnipotent τ K' := by
  rw [Subgroup.map_le_iff_le_comap]
  conv_lhs => rw [negUnipotent, rootSpan]
  refine iSup_le fun α => iSup_le fun hα => ?_
  rw [rootSubgroup, Subgroup.closure_le]
  rintro g ⟨c, rfl⟩
  exact Subgroup.mem_comap.2 (by
    rw [negUnipotent, rootSpan]
    exact Subgroup.mem_iSup_of_mem α (Subgroup.mem_iSup_of_mem hα
      (Subgroup.subset_closure ⟨f c, (baseChangeGL_pinnedX f α c).symm⟩)))

private theorem bcGL937_twistedFixedGroup_le
    {K K' : Type} [Field K] [Field K'] (f : K →+* K')
    (σ : K →+* K) (σ' : K' →+* K') (h : ∀ c, σ' (f c) = f (σ c)) :
    (twistedFixedGroup TwistTag.E6 K σ).map (baseChangeGL f) ≤
      twistedFixedGroup TwistTag.E6 K' σ' := by
  rintro _ ⟨g, hg, rfl⟩
  change g ∈ twistedFixedGroup TwistTag.E6 K σ at hg
  rw [mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ] at hg
  rw [mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K' σ']
  refine ⟨baseChangeGL_mem_adjointGroup f hg.1, ?_⟩
  rw [twistHom_baseChangeGL f (RingHom.ext fun c => (h c).symm), hg.2]

private theorem bcGL937_le_graphFixedRootGroup
    {K K' : Type} [Field K] [Field K'] (f : K →+* K')
    (σ : K →+* K) (σ' : K' →+* K') (h : ∀ c, σ' (f c) = f (σ c)) :
    (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL f) ≤
      graphFixedRootGroup TwistTag.E6 K' σ' := by
  rw [graphFixedRootGroup, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · have hpos : (graphFixedPosUnipotent TwistTag.E6 K σ).map (baseChangeGL f) ≤
        graphFixedPosUnipotent TwistTag.E6 K' σ' := by
      rw [graphFixedPosUnipotent]
      exact le_trans (Subgroup.map_inf_le _ _ _)
        (inf_le_inf (bcGL937_posUnipotent_le f)
          (bcGL937_twistedFixedGroup_le f σ σ' h))
    exact le_trans hpos (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _)
  · have hneg : (graphFixedNegUnipotent TwistTag.E6 K σ).map (baseChangeGL f) ≤
        graphFixedNegUnipotent TwistTag.E6 K' σ' := by
      rw [graphFixedNegUnipotent]
      exact le_trans (Subgroup.map_inf_le _ _ _)
        (inf_le_inf (bcGL937_negUnipotent_le f)
          (bcGL937_twistedFixedGroup_le f σ σ' h))
    exact le_trans hneg (graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _)

private theorem bcGL937_id_apply
    {K : Type} [Field K] {τ : Tag} (g : ModGL τ K) :
    baseChangeGL (RingHom.id K) g = g :=
  Units.ext ((baseChange_baseChangeEnd (RingHom.id K)
    (g : Module.End K (RootModule τ K))).unique fun b => by simp)

private theorem bcGL937_id_local
    {K : Type} [Field K] {τ : Tag} (H : Subgroup (ModGL τ K)) :
    H.map (baseChangeGL (RingHom.id K)) = H := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    rwa [bcGL937_id_apply]
  · intro hg
    exact ⟨g, hg, bcGL937_id_apply g⟩

private theorem bcGL937_graphFixedRootGroup_eq
    {K K' : Type} [Field K] [Field K'] (e : K ≃+* K')
    (σ : K →+* K) (σ' : K' →+* K') (h : ∀ c, σ' (e c) = e (σ c)) :
    (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL e.toRingHom) =
      graphFixedRootGroup TwistTag.E6 K' σ' := by
  refine le_antisymm (bcGL937_le_graphFixedRootGroup e.toRingHom σ σ' h) ?_
  have hsymm : ∀ c : K', σ (e.symm c) = e.symm (σ' c) := fun c => by
    have hc : σ' c = e (σ (e.symm c)) := by
      simpa using h (e.symm c)
    exact e.injective (by rw [RingEquiv.apply_symm_apply]; exact hc.symm)
  have hback : (graphFixedRootGroup TwistTag.E6 K' σ').map
      (baseChangeGL e.symm.toRingHom) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    bcGL937_le_graphFixedRootGroup e.symm.toRingHom σ' σ hsymm
  have hmono := Subgroup.map_mono (f := baseChangeGL e.toRingHom) hback
  have hcompGL : (baseChangeGL (τ := TwistTag.E6.tag) e.toRingHom).comp
        (baseChangeGL (τ := TwistTag.E6.tag) e.symm.toRingHom) =
      baseChangeGL (τ := TwistTag.E6.tag) (RingHom.id K') := by
    ext x
    rw [MonoidHom.comp_apply, baseChangeGL_baseChangeGL,
      show e.toRingHom.comp e.symm.toRingHom = RingHom.id K' from RingHom.ext fun c => by simp]
  have hmap : ((graphFixedRootGroup TwistTag.E6 K' σ').map
        (baseChangeGL e.symm.toRingHom)).map (baseChangeGL e.toRingHom) =
      graphFixedRootGroup TwistTag.E6 K' σ' := by
    rw [Subgroup.map_map, hcompGL, bcGL937_id_local]
  rw [hmap] at hmono
  exact hmono

theorem graphFixedRootGroup_mulEquiv_of_ringEquiv
    {K K' : Type} [Field K] [Field K']
    (e : K ≃+* K') (σ : K →+* K) (σ' : K' →+* K') (h : ∀ c, σ' (e c) = e (σ c)) :
    Nonempty (↥(graphFixedRootGroup TwistTag.E6 K σ) ≃* ↥(graphFixedRootGroup TwistTag.E6 K' σ')) :=
  ⟨(Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.E6 K σ)
      (baseChangeGL e.toRingHom) (baseChangeGL_injective e.toRingHom)).trans
    (MulEquiv.subgroupCongr (bcGL937_graphFixedRootGroup_eq e σ σ' h))⟩

end Transport

end Irred937

end CFSG.StandardType
