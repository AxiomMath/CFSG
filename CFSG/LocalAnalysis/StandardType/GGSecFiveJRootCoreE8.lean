module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreTorus
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreExcAdj
import CFSG.LocalAnalysis.StandardType.GGSteinbergAutLemmas
import CFSG.LieType.Steinberg.Adjoint.Borel
import CFSG.LieType.Chevalley.PerfectSimpleRoot

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Adjoint

private theorem jcoreE8_mem_torusGroup
    {K : Type} [Field K] [Finite K] {u : adjointGroup .E8 K} (hu : u ∈ ggTorus (e8Datum K)) :
    (u : ModGL .E8 K) ∈ torusGroup .E8 K := by
  have : Finite (adjointGroup .E8 K) := generated_group_finite .E8 K
  rw [SteinbergAut.ggTorus_eq_iSup (e8_isCTGroupDatum K) (e8_steinbergExtras K)
    (e8_bruhatExtras K)] at hu
  have hle : (⨆ i, torus (τ := .E8) K i) ≤
      (torusGroup .E8 K).comap (adjointGroup .E8 K).subtype := iSup_le fun i => by
    rintro _ ⟨s, rfl⟩
    exact Subgroup.subset_closure ⟨(i, s), rfl⟩
  exact hle hu

theorem jcore_E8_torus :
    GGJRootCoreTorusAt .E8 := by
  intro n f hadm _ p hp hp2 hpf u hu hup J hJ
  obtain ⟨-, hf, -⟩ := hadm
  obtain ⟨t, ht⟩ := jcoreE_exists_unit hf hp hp2 hpf
  obtain ⟨γ, hγ, hle⟩ := jcoreE_adj_rootLevi (rootOperatorFamily .E8) hp ht
    (jcoreE8_mem_torusGroup (K := GaloisField 2 f) hu) hup hJ
  exact ⟨γ, (mem_adjDatum_roots (F := rootOperatorFamily .E8) (K := GaloisField 2 f)).2 hγ, hle⟩

end CFSG.StandardType

end
