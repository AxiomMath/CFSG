module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart28

@[expose] public section

public noncomputable section
variable {K : Type} [Field K] [CharP K 2] [Finite K]

namespace CFSG.StandardType.F4ExplicitPos.C3Range
open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed

theorem c3RootSubgroup_eq_rootGroup {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    c3RootSubgroup (K := K) γ
      = (CFSG.LieType.Universal.Symplectic.rootDatum 3 K).rootGroup γ := by
  have hp := Sp.isParametrization (n := 3) (F := K) γ (by rwa [Sp.Φ_roots])
  rw [c3RootSubgroup]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact (hp.1 _).2 ⟨c, rfl⟩
  · intro g hg
    obtain ⟨c, rfl⟩ := (hp.1 g).1 hg
    exact Subgroup.subset_closure ⟨c, rfl⟩

theorem iSup_c3RootSubgroup_eq_top :
    (⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅, c3RootSubgroup (K := K) γ)
      = ⊤ := by
  rw [show (⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅, c3RootSubgroup (K := K) γ)
      = ⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
          (CFSG.LieType.Universal.Symplectic.rootDatum 3 K).rootGroup γ from
    iSup_congr fun γ => iSup_congr fun hγ => c3RootSubgroup_eq_rootGroup (K := K) hγ]
  exact (CFSG.LieType.Universal.Symplectic.isCTGroupDatum 3 K).iSup_eq_top

theorem range_eq_rootSpan
    (ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K))
    (hι : ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c) :
    MonoidHom.range ((adjointGroup .F4 K).subtype.comp ι)
      = CFSG.Blueprint.Chevalley.rootSpan .F4 K c3RootSet := by
  let f : ↥(StatedSp 3 K) →* ModGL .F4 K := (adjointGroup .F4 K).subtype.comp ι
  have key : MonoidHom.range f
      = ⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
          CFSG.Blueprint.Chevalley.rootSubgroup .F4 K (c3ToF4 γ) := by
    rw [MonoidHom.range_eq_map, ← iSup_c3RootSubgroup_eq_top (K := K)]
    simp only [Subgroup.map_iSup]
    exact iSup_congr fun γ => iSup_congr fun hγ =>
      map_c3RootSubgroup_eq_rootSubgroup ι hι hγ
  rw [key]
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ c3RootSet) =>
        CFSG.Blueprint.Chevalley.rootSubgroup .F4 K α) (c3ToF4 γ) ⟨γ, hγ, rfl⟩ le_rfl
  · rw [CFSG.Blueprint.Chevalley.rootSpan]
    refine iSup₂_le fun α hα => ?_
    obtain ⟨γ, hγ, rfl⟩ := hα
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ roots (isFiniteType_cartanC 3) ∅) =>
        CFSG.Blueprint.Chevalley.rootSubgroup .F4 K (c3ToF4 γ)) γ hγ le_rfl

theorem f4C3_exists_pinned_full :
    ∃ ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K), Function.Injective ι ∧
      (MonoidHom.range ((adjointGroup .F4 K).subtype.comp ι)
        = CFSG.Blueprint.Chevalley.rootSpan .F4 K c3RootSet) ∧
      (∀ {γ : Fin 3 → ℤ}, γ ∈ roots (isFiniteType_cartanC 3) ∅ → ∀ c,
        ((ι (Sp.x 3 K γ c) : ↥(adjointGroup .F4 K)) : ModGL .F4 K)
          = pinnedX .F4 K (c3ToF4 γ)
              (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) * c)) ∧
      (∀ {γ : Fin 3 → ℤ}, γ ∈ roots (isFiniteType_cartanC 3) ∅ →
        (c3RootSubgroup (K := K) γ).map ((adjointGroup .F4 K).subtype.comp ι)
          = CFSG.Blueprint.Chevalley.rootSubgroup .F4 K (c3ToF4 γ)) := by
  obtain ⟨ι, hinj, hform⟩ := CFSG.StandardType.F4ExplicitPos.C3Comm.f4C3_exists_pinned_unconditional
    (CFSG.Timmesfeld.Transvection.Pres.spOrder 3 K)
  exact ⟨ι, hinj, range_eq_rootSpan ι hform,
    fun hγ c => iota_x_eq_pinnedX ι hform hγ c,
    fun hγ => map_c3RootSubgroup_eq_rootSubgroup ι hform hγ⟩

end CFSG.StandardType.F4ExplicitPos.C3Range

end

end
