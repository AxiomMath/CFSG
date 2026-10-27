module

public import CFSG.Quasithin.H13.GoldschmidtC137Pt3Aux
public import CFSG.Quasithin.H13.GoldschmidtC137CPt1

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace C137FrameB

variable [Finite G] {X T V L P : Subgroup G} {h : C137Base X T V L P} (F : C137FrameB h)

theorem autI_baum_eq_Z1 (hR : autI h.hVe (pCoreOf 2 P) = R1.map F.ρ)
    (hJ1 : autI h.hVe (thompsonJ (pCoreOf 2 P)) = Z1.map F.ρ) :
    autI h.hVe (baum (pCoreOf 2 P)) = Z1.map F.ρ := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨hφR, hφc⟩ := autI_baum_le h.hVe h.toBaum.hVR h.R_le_N hφ
    rw [hR] at hφR
    obtain ⟨σ, hσ, rfl⟩ := hφR
    rw [hJ1] at hφc
    have hφc' : ∀ u ∈ fixV (Z1.map F.ρ), F.ρ σ u = u := hφc
    have hfix : fixV (Z1.map (Mod.act 6 F.k)) = (fixV (Z1.map F.ρ)).map F.Φ.toMonoidHom := by
      rw [← F.map_θ_map_ρ Z1]
      exact fixV_map F.Φ (Z1.map F.ρ)
    refine ⟨σ, R1_cent_fix hσ fun v hv => ?_, rfl⟩
    rw [← fixV_map_projK F.hk Z1, hfix] at hv
    obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hv
    show Mod.act 6 Mod.ut0 σ (projK F.k (F.Φ u)) = projK F.k (F.Φ u)
    rw [← projK_act F.hk, ← F.equiv, hφc' u hu]
  · rw [← hJ1]
    exact autI_mono h.hVe (B2F.thompsonJ_le_baum _)


end C137FrameB

end CFSG.Quasithin.H13.U3.GC137
