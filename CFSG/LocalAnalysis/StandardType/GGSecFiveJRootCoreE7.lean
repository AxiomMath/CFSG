module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreTorus
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreExcAdj
import CFSG.LocalAnalysis.StandardType.GGSteinbergAutLemmas
import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivExcToral
import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
import CFSG.LieType.Steinberg.Isogeny.E7
import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.E7Rep
import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverCentral

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.SeitzReduction.E8Pilot

private theorem jcoreE7_mem_torusGroup
    {K : Type} [Field K] [Finite K] {u : ↥(e7Data_valid.minGroup K)}
    (hu : u ∈ ggTorus (e7Datum K)) :
    ((e7Isogeny K u : adjointGroup .E7 K) : ModGL .E7 K) ∈ torusGroup .E7 K := by
  have : Finite (Module.End K (Fin e7Data.d →₀ K)) := Module.finite_of_finite K
  have : Finite ↥(e7Data_valid.minGroup K) := Subtype.finite
  rw [SteinbergAut.ggTorus_eq_iSup (e7Datum_isCTGroupDatum K) (e7Datum_steinbergExtras K)
    (e7Datum_bruhatExtras K)] at hu
  have hle : (⨆ i, e7Data_valid.torus K i) ≤ (torusGroup .E7 K).comap
      ((adjointGroup .E7 K).subtype.comp (e7Isogeny K)) := iSup_le fun i => by
    rintro _ ⟨s, rfl⟩
    change ((e7Isogeny K (e7Data_valid.hm K i s) : adjointGroup .E7 K) : ModGL .E7 K) ∈
      torusGroup .E7 K
    rw [CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.e7Isogeny_hm]
    exact Subgroup.subset_closure ⟨(i, s), rfl⟩
  exact hle hu

private theorem jcoreE7_levi
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) {t : Kˣ}
    (ht : (t : K) ^ 2 ≠ 1) {u : ↥(e7Data_valid.minGroup K)} (hu : u ∈ ggTorus (e7Datum K))
    (hup : u ^ p = 1) {J : Subgroup ↥(e7Data_valid.minGroup K)}
    (hJ : IsComponentOf J (Subgroup.centralizer {u})) :
    ∃ γ ∈ (e7Datum K).roots, ggRootLevi (e7Datum K) γ ≤ J := by
  have hJ' : IsComponentOf (J.map (e7MinEquivAdjoint K).toMonoidHom)
      (Subgroup.centralizer {e7MinEquivAdjoint K u}) := by
    rw [← LayerPDivExc.map_centralizer_singleton (e7MinEquivAdjoint K) u]
    exact LayerPDivExc.isComponentOf_map (e7MinEquivAdjoint K).injective hJ
  have hv : ((e7MinEquivAdjoint K u : adjointGroup .E7 K) : ModGL .E7 K) ∈ torusGroup .E7 K :=
    jcoreE7_mem_torusGroup hu
  have hvp : e7MinEquivAdjoint K u ^ p = 1 := by rw [← map_pow, hup, map_one]
  obtain ⟨γ, hγ, hle⟩ := jcoreE_adj_rootLevi (rootOperatorFamily .E7) hp ht hv hvp hJ'
  have key : ∀ δ, IsRoot .E7 δ →
      rootGroup (rootOperatorFamily .E7) K δ ≤ J.map (e7MinEquivAdjoint K).toMonoidHom →
      (e7Datum K).rootGroup δ ≤ J := by
    intro δ hδ hδJ y hy
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hy
    have h1 : e7MinEquivAdjoint K (e7Data_valid.xm K δ c) ∈
        J.map (e7MinEquivAdjoint K).toMonoidHom := hδJ (by
      rw [e7MinEquivAdjoint_apply, e7Isogeny_xm]
      exact xPar_mem hδ _)
    rwa [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at h1
  exact ⟨γ, (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).2 hγ,
    sup_le (key γ hγ (le_sup_left.trans hle)) (key (-γ) (IsRoot.neg hγ) (le_sup_right.trans hle))⟩

theorem jcore_E7_torus :
    GGJRootCoreTorusAt .E7 := by
  intro n f hadm _ p hp hp2 hpf u hu hup J hJ
  obtain ⟨-, hf, -⟩ := hadm
  obtain ⟨t, ht⟩ := jcoreE_exists_unit hf hp hp2 hpf
  exact jcoreE7_levi (K := GaloisField 2 f) hp ht hu hup hJ

end CFSG.StandardType

end
