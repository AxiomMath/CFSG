module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StronglyEmbedded.SteinbergBU

open Subgroup

variable {G : Type*} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g x : G} : x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    change g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹ ∈ H
    rw [show g * (g⁻¹ * h * g⁻¹⁻¹) * g⁻¹ = h by group]
    exact hh
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by change g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x; group⟩

theorem conjugate_eq_self_iff {K : Subgroup G} {g : G} :
    conjugate K g = K ↔ g ∈ normalizer (K : Set G) := by
  rw [mem_normalizer_iff]
  constructor
  · intro hK h
    constructor
    · intro hh
      rw [← hK] at hh
      exact mem_conjugate_iff.1 hh
    · intro hh
      rw [← hK]
      exact mem_conjugate_iff.2 hh
  · intro hg
    ext h
    rw [mem_conjugate_iff]
    exact (hg h).symm

variable [Finite G]

end CFSG.StronglyEmbedded.SteinbergBU
