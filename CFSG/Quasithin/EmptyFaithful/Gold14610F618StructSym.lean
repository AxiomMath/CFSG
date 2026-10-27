module

public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructIso

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Gold14610

namespace Struct

variable {D : Type} [Group D]

theorem sq_mem_alternatingGroup {α : Type} [DecidableEq α] [Fintype α] (σ : Equiv.Perm α) :
    σ ^ 2 ∈ alternatingGroup α := by
  rw [Equiv.Perm.mem_alternatingGroup, map_pow]
  exact Int.units_sq _

theorem idx2Data_of_isHatSym {n : ℕ} (hcore : ∀ (Y : Type) [Group Y], F6.IsHatAlt n Y → F618Core Y)
    (h : F6.IsHatSym n D) : Idx2Data D := by
  obtain ⟨φ, -, -, hA⟩ := h
  refine ⟨(alternatingGroup (Fin n)).comap φ, inferInstance, hcore _ hA,
    fun x => ?_, Or.inr ?_⟩
  · rw [Subgroup.mem_comap, map_pow]
    exact sq_mem_alternatingGroup _
  · exact (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr hA.1

theorem idx2Data_of_isHatSym_six (h : F6.IsHatSym 6 D) : Idx2Data D :=
  idx2Data_of_isHatSym (fun _ _ hA => Or.inr (Or.inr (Or.inl hA))) h

theorem idx2Data_of_isHatSym_seven (h : F6.IsHatSym 7 D) : Idx2Data D :=
  idx2Data_of_isHatSym (fun _ _ hA => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA))))) h

theorem idx2Data_of_perm_seven (h : Nonempty (D ≃* Equiv.Perm (Fin 7))) : Idx2Data D := by
  obtain ⟨e⟩ := h
  refine Idx2Data.of_mulEquiv e ⟨alternatingGroup (Fin 7), inferInstance,
    Or.inr (Or.inr (Or.inr (Or.inl ⟨MulEquiv.refl _⟩))), fun x => sq_mem_alternatingGroup x,
    Or.inl ?_⟩
  exact alternatingGroup.isSimpleGroup (by simp)

end Struct

end Gold14610

end CFSG.Quasithin
