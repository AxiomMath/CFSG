module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.LocalAnalysis.StandardType.FS81.S7Model

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.E7Pilot
open CFSG.QuasithinUnique
open scoped commutatorElement

variable {M G : Type} [Group M] [Group G]

theorem isSylow2In_map_of_injective (φ : M →* G) (hφ : Function.Injective φ) {S T : Subgroup M}
    (hST : IsSylow2In S T) : IsSylow2In (S.map φ) (T.map φ) := by
  obtain ⟨hle, hp, hmax⟩ := hST
  refine ⟨Subgroup.map_mono hle, hp.map φ, ?_⟩
  intro V hV hVp hSV
  have hVr : V ≤ φ.range := hV.trans (Subgroup.map_le_range φ T)
  have hVV : (V.comap φ).map φ = V := Subgroup.map_comap_eq_self hVr
  have hVT : V.comap φ ≤ T := fun x hx =>
    (Subgroup.mem_map_iff_mem hφ).1 (hV (Subgroup.mem_comap.1 hx))
  have hVp' : IsPGroup 2 (V.comap φ) := hVp.comap_of_injective φ hφ
  have hSV' : S ≤ V.comap φ := Subgroup.map_le_iff_le_comap.1 hSV
  rw [← hVV, hmax (V.comap φ) hVT hVp' hSV']

theorem fs81CommSet_map (φ : M →* G) (Q : Subgroup M) (σ : M) :
    fs81CommSet (Q.map φ) (φ σ) = φ '' fs81CommSet Q σ := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    exact ⟨⁅q₀, σ⁆, ⟨q₀, hq₀, rfl⟩, map_commutatorElement φ q₀ σ⟩
  · rintro ⟨w, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨φ q, Subgroup.mem_map_of_mem φ hq, map_commutatorElement φ q σ⟩

theorem fs81SigmaW_map (φ : M →* G) (Q : Subgroup M) (σ t : M) :
    (fs81SigmaW Q σ t).map φ = fs81SigmaW (Q.map φ) (φ σ) (φ t) := by
  unfold fs81SigmaW
  rw [Subgroup.map_sup, MonoidHom.map_closure, MonoidHom.map_zpowers, fs81CommSet_map]

end CFSG.StandardType.FrameRoute.FS81
