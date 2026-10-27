module

public import CFSG.Quasithin.H13.GoldschmidtC137CFrame
public import CFSG.Quasithin.H13.GoldschmidtC137KMod1

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace C137Frame

variable [Finite G] {V X T L : Subgroup G} {hVe : IsElemAbelian 2 V} (F : C137Frame hVe X T L)

include F in
theorem card_V : Nat.card (IntMod V hVe) = 16 * cK F.k := by
  rw [Nat.card_congr F.Φ.toEquiv, card_modV F.hk]

theorem card_ρ (K : Subgroup (Gp 6)) : Nat.card (K.map F.ρ) = Nat.card K :=
  Subgroup.card_map_of_injective F.inj

theorem card_fixV_ρ (K : Subgroup (Gp 6)) :
    Nat.card (fixV (K.map F.ρ)) = cK F.k * Nat.card (fixV (K.map (Mod.act 6 Mod.ut0))) := by
  calc Nat.card (fixV (K.map F.ρ))
      = Nat.card (fixV ((K.map F.ρ).map F.θ.toMonoidHom)) := (card_fixV_map F.Φ _).symm
    _ = Nat.card (fixV (K.map (Mod.act 6 F.k))) := by rw [F.map_θ_map_ρ K]
    _ = _ := card_fixV_act F.hk K

theorem rkIdx_fixV_ρ (K : Subgroup (Gp 6)) :
    rkIdx (fixV (K.map F.ρ)) = rkIdx (fixV (K.map (Mod.act 6 Mod.ut0))) := by
  calc rkIdx (fixV (K.map F.ρ)) = rkIdx (fixV ((K.map F.ρ).map F.θ.toMonoidHom)) :=
        (rkIdx_fixV_map F.Φ _).symm
    _ = rkIdx (fixV (K.map (Mod.act 6 F.k))) := by rw [F.map_θ_map_ρ K]
    _ = _ := rkIdx_fixV_act F.hk K

theorem rAV_ρ (K : Subgroup (Gp 6)) :
    rAV (K.map F.ρ) = rAV (K.map (Mod.act 6 Mod.ut0)) := by
  calc rAV (K.map F.ρ) = rAV ((K.map F.ρ).map F.θ.toMonoidHom) := (rAV_map F.Φ _).symm
    _ = rAV (K.map (Mod.act 6 F.k)) := by rw [F.map_θ_map_ρ K]
    _ = _ := rAV_act F.hk K

theorem offender_ρ (A : Subgroup (Gp 6)) :
    IsFFStarOffender (autI hVe X) (A.map F.ρ) ↔ IsOffG 6 Mod.ut0 A := by
  unfold IsOffG
  rw [← isFFStarOffender_act_iff F.hk, ← F.map_θ_map_ρ A, ← F.map_θ_map_ρ ⊤, ← F.hX]
  exact (isFFStarOffender_map_iff F.Φ).symm

end C137Frame

end CFSG.Quasithin.H13.U3.GC137
