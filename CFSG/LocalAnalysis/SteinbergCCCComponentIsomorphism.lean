module

public import CFSG.Foundations.Basic

public section

namespace CFSG.LocalAnalysis

open Subgroup

namespace CComponentIsomorphism

theorem map {G H : Type*} [Group G] [Group H] (f : G ≃* H) {L : Subgroup G}
    (hL : IsCComponent L) : IsCComponent (L.map f.toMonoidHom) := by
  obtain ⟨hL1, hLp, hLs, hLmin⟩ := hL
  have hsymm : ∀ M : Subgroup G, (M.map f.toMonoidHom).map f.symm.toMonoidHom = M := fun M => by
    rw [map_map]
    convert map_id M
    ext x
    simp
  refine ⟨fun h => hL1 ((map_eq_bot_iff_of_injective L f.injective).mp h), ?_,
    hLs.map f.surjective, fun K hK hK1 hKp hKs => ?_⟩
  · rw [← map_commutator, hLp]
  · have hK' : K.map f.symm.toMonoidHom < L := by
      rw [← hsymm L]
      exact (map_lt_map_iff_of_injective f.symm.injective).mpr hK
    refine hLmin _ hK' (fun h => hK1 ?_) (by rw [← map_commutator, hKp])
      (hKs.map f.symm.surjective)
    have h2 := congrArg (Subgroup.map f.toMonoidHom) h
    rw [Subgroup.map_bot, map_map] at h2
    rw [← h2]
    convert (map_id K).symm
    ext x
    simp

end CComponentIsomorphism

end CFSG.LocalAnalysis
