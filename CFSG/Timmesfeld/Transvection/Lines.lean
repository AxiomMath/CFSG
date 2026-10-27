module

public import CFSG.Timmesfeld.Transvection.Defs

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS

variable {H : Type*} [Group H]

@[expose] def lineOf (Δ : Set (Subgroup H)) (A B : Subgroup H) : Set (Subgroup H) :=
  {D | D ∈ Δ ∧ ∀ X ∈ Δ, Commuting X A → Commuting X B → Commuting X D}

@[expose] def MeetsLines (Δ : Set (Subgroup H)) : Prop :=
  ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commuting A B → ∀ C ∈ Δ, ∃ D ∈ lineOf Δ A B, Commuting C D

variable {Δ : Set (Subgroup H)} {A B : Subgroup H}

theorem left_mem_lineOf (hA : A ∈ Δ) : A ∈ lineOf Δ A B :=
  ⟨hA, fun _ _ h _ => h⟩

theorem right_mem_lineOf (hB : B ∈ Δ) : B ∈ lineOf Δ A B :=
  ⟨hB, fun _ _ _ h => h⟩

theorem thickLines_iff : ThickLines Δ ↔ ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → Commuting A B →
    ∃ C ∈ lineOf Δ A B, C ≠ A ∧ C ≠ B := by
  constructor
  · intro h A hA B hB hAB hc
    obtain ⟨C, hC, hCA, hCB, hD⟩ := h A hA B hB hAB hc
    exact ⟨C, ⟨hC, hD⟩, hCA, hCB⟩
  · intro h A hA B hB hAB hc
    obtain ⟨C, ⟨hC, hD⟩, hCA, hCB⟩ := h A hA B hB hAB hc
    exact ⟨C, hC, hCA, hCB, hD⟩

end CFSG.Timmesfeld.Transvection
