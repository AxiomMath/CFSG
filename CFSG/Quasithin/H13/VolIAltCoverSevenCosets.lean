module

public import CFSG.Quasithin.H13.VolIAltCoverSevenData

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin Equiv

@[expose] def a7reps6 : List ↥(alternatingGroup (Fin 7)) :=
  [1, a7c234, a7c234 * a7c234, a7c012 * a7c234, a7c012 * a7c012 * a7c234, a7s * a7s * a7c234]

theorem a7reps6_fix : ∀ h ∈ a7reps6, (h : Perm (Fin 7)) 6 = 6 := by decide +kernel

theorem alt7_cosets6 : ∀ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) 6 = 6 ∨
    ∃ h ∈ a7reps6, (((h * a7c456)⁻¹ * σ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) 6 = 6 := by
  decide +kernel

end CFSG.Quasithin.H13.VolI
