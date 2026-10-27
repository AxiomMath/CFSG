module

public import CFSG.Milestones.ASVolI.F437.Defs
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

section Kinds

variable {E : Type} [Group E] {Gp : Subgroup E} {κ : GLKind} {degree : ℕ}

theorem burnsideF437_graph_kind {chart : NativeChart κ 2 degree Gp} {t : E}
    (h : chart.IsGraphInv t) : κ = .U4 ∨ κ = .U5 := by
  obtain ⟨-, -, -, conj, -, hpure⟩ := h
  revert hpure
  generalize chart.coordinatePayload = coords
  intro hpure
  cases coords with
  | classical m hm marking =>
    obtain ⟨hm', -⟩ := hpure
    rcases hm' with rfl | rfl
    · exact Or.inl hm
    · exact Or.inr hm
  | g2 => exact hpure.elim
  | g2Derived => exact hpure.elim
  | triality => exact hpure.elim
  | ree => exact hpure.elim
  | tits => exact hpure.elim

theorem burnsideF437_field_kind {chart : NativeChart κ 2 degree Gp} {t : E}
    (h : chart.IsFieldInv t) : κ ≠ .U4 ∧ κ ≠ .U5 := by
  obtain ⟨-, -, sd, -, -, conj, -, hpure⟩ := h
  revert hpure
  generalize chart.coordinatePayload = coords
  intro hpure
  cases coords with
  | classical m hm marking =>
    obtain ⟨hm', -⟩ := hpure
    rcases hm' with rfl | rfl
    · rw [hm]; exact ⟨by decide, by decide⟩
    · rw [hm]; exact ⟨by decide, by decide⟩
  | g2 hk => rw [hk]; exact ⟨by decide, by decide⟩
  | g2Derived => exact hpure.elim
  | triality hk => rw [hk]; exact ⟨by decide, by decide⟩
  | ree => exact hpure.elim
  | tits => exact hpure.elim

end Kinds

theorem burnsideF437_classInput_of_F_4_29 (h : F_4_29) : burnsideF437_ClassInput := by
  intro κ degree E _ Gp M₁ M₂ hyp hκ T hT t ht htS htt
  rcases (h κ degree E Gp M₁ M₂ hyp hκ T hT).2.1.2.2 t ht htS htt with h1 | h2 | ⟨h3, -⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)

end CFSG.ASVolI
