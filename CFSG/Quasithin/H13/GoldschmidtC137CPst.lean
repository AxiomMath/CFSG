module

public import CFSG.Quasithin.H13.GoldschmidtC137CBase

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace C137FrameB

variable [Finite G] {X T V L P : Subgroup G} {h : C137Base X T V L P} (F : C137FrameB h)

theorem map_KP : (F.KP P).map F.ρ = autI h.hVe P :=
  F.map_comap_eq (autI_mono h.hVe h.hPX.le)

theorem T6_le_KP : T6 ≤ (F.KP P) := fun σ hσ => by
  show F.ρ σ ∈ autI h.hVe P
  have hmem : F.ρ σ ∈ T6.map F.ρ := ⟨σ, hσ, rfl⟩
  rw [F.hT] at hmem
  exact autI_mono h.hVe h.hTP hmem

end C137FrameB

end CFSG.Quasithin.H13.U3.GC137
