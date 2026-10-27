module

public import CFSG.Timmesfeld.ARS.Sec12Meets
public import CFSG.Timmesfeld.Transvection.Lines

public section

namespace CFSG.Timmesfeld.ARS

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem meetsLines_restrict :
    Transvection.MeetsLines (restrict (leviSet R A A₀) (levi R A A₀)) := by
  have hcomm : ∀ {P Q : Subgroup G}, P ≤ levi R A A₀ → Q ≤ levi R A A₀ →
      (Commuting (P.subgroupOf (levi R A A₀)) (Q.subgroupOf (levi R A A₀)) ↔ Commuting P Q) := by
    intro P Q hP hQ
    rw [Restrict.commuting_subgroupOf_iff, inf_of_le_left hP, inf_of_le_left hQ]
  have hle : ∀ {X : Subgroup G}, X ∈ leviSet R A A₀ → X ≤ levi R A A₀ := fun hX _ hx =>
    le_gen hX hx
  rintro _ ⟨X, ⟨hX, hXV⟩, rfl⟩ _ ⟨Y, ⟨hY, hYV⟩, rfl⟩ hXY hc _ ⟨W, ⟨hW, hWV⟩, rfl⟩
  have hXY' : X ≠ Y := fun h => hXY (by rw [h])
  obtain ⟨Z, hZ, hZW, hZline⟩ := hS.exists_commuting_mem_line hX hY hXY'
    ((hcomm hXV hYV).1 hc) hW
  refine ⟨Z.subgroupOf (levi R A A₀), ⟨⟨Z, ⟨hZ, hle hZ⟩, rfl⟩, ?_⟩,
    (hcomm hWV (hle hZ)).2 hZW.symm⟩
  rintro _ ⟨U, ⟨hU, hUV⟩, rfl⟩ hUX hUY
  exact (hcomm hUV (hle hZ)).2 (hZline U hU ((hcomm hUV hXV).1 hUX) ((hcomm hUV hYV).1 hUY))

end Sec12

end CFSG.Timmesfeld.ARS
