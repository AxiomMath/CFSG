module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Subgroup

variable {G H : Type*} [Group G] [Group H] {ℓ : ℕ}

theorem InspPair.of_map_equiv (e : G ≃* H) {D : Subgroup G} {R' : Subgroup H}
    (h : InspPair ℓ (D.map e.toMonoidHom) R') :
    InspPair ℓ D (R'.map e.symm.toMonoidHom) := by
  have h' := h.map e.symm
  have hDe : (D.map e.toMonoidHom).map e.symm.toMonoidHom = D := by
    rw [Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
      ext x; simp
    rw [this, Subgroup.map_id]
  rw [hDe] at h'
  exact h'

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
