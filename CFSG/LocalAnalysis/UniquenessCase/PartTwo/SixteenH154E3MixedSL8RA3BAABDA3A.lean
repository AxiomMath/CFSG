module

public import CFSG.Quasithin.Background.HLUBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.LU Subgroup

variable {W : Type} [CommGroup W]

theorem s16h_autSub_card_map_conj (X : Subgroup (MulAut W)) (U : Subgroup W) (t : MulAut W) :
    Nat.card ↥(autSub (X.map (MulAut.conj t).toMonoidHom) (U.map t.toMonoidHom)) =
      Nat.card ↥(autSub X U) := by
  have hcongr : congrHom t = (MulAut.conj t).toMonoidHom :=
    MonoidHom.ext fun x => MulEquiv.ext fun w => by
      simp [congrHom_apply, MulAut.conj_apply]
  have hU : ∀ v, v ∈ U ↔ t v ∈ U.map t.toMonoidHom := by
    intro v
    rw [Subgroup.mem_map]
    exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, hwv⟩ => t.injective hwv ▸ hw⟩
  have h := autSub_map (U' := U.map t.toMonoidHom) t X hU
  rw [hcongr] at h
  rw [h, Subgroup.card_map_of_injective (K := autSub X U)
    (f := congrHom (resEquiv t hU)) (congrHom_injective (resEquiv t hU))]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
