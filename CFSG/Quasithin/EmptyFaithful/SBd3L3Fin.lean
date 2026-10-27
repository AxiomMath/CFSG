module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin

namespace SBd3

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

abbrev SL3 : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

@[expose] def cond1 (g : SL3) : Prop :=
  (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0

@[expose] def cond2 (g : SL3) : Prop :=
  (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0

@[expose] def condB (g : SL3) : Prop :=
  (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 0 = 0 ∧
    (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) 2 1 = 0

theorem mem_upperTriangular_iff (g : SL3) : g ∈ upperTriangular 3 (ZMod 2) ↔ condB g := by
  constructor
  · intro h
    exact ⟨h 1 0 (by decide), h 2 0 (by decide), h 2 1 (by decide)⟩
  · rintro ⟨h1, h2, h3⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> assumption

theorem cond1_of_mem_stabilizer {g : SL3} (h : g ∈ stabilizer (flagSpace 3 (ZMod 2) 1)) :
    cond1 g := by
  have hmv : ∀ v ∈ flagSpace 3 (ZMod 2) 1, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v ∈ flagSpace 3 (ZMod 2) 1 :=
    fun v hv => by
    rw [← mem_stabilizer.mp h]
    exact ⟨v, hv, rfl⟩
  have hv : (Pi.single 0 1 : Fin 3 → ZMod 2) ∈ flagSpace 3 (ZMod 2) 1 :=
    mem_flagSpace.mpr fun j hj => Pi.single_eq_of_ne (by rintro rfl; simp at hj) _
  have e1 := mem_flagSpace.mp (hmv _ hv)
  exact ⟨by simpa [mulVec, dotProduct, Fin.sum_univ_three] using e1 1 (by decide),
    by simpa [mulVec, dotProduct, Fin.sum_univ_three] using e1 2 (by decide)⟩


theorem cond2_of_mem_stabilizer {g : SL3} (h : g ∈ stabilizer (flagSpace 3 (ZMod 2) 2)) :
    cond2 g := by
  have hmv : ∀ v ∈ flagSpace 3 (ZMod 2) 2, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v ∈ flagSpace 3 (ZMod 2) 2 :=
    fun v hv => by
    rw [← mem_stabilizer.mp h]
    exact ⟨v, hv, rfl⟩
  have hv0 : (Pi.single 0 1 : Fin 3 → ZMod 2) ∈ flagSpace 3 (ZMod 2) 2 :=
    mem_flagSpace.mpr fun j hj => Pi.single_eq_of_ne (by rintro rfl; simp at hj) _
  have hv1 : (Pi.single 1 1 : Fin 3 → ZMod 2) ∈ flagSpace 3 (ZMod 2) 2 :=
    mem_flagSpace.mpr fun j hj => Pi.single_eq_of_ne (by rintro rfl; simp at hj) _
  have e0 := mem_flagSpace.mp (hmv _ hv0)
  have e1 := mem_flagSpace.mp (hmv _ hv1)
  exact ⟨by simpa [mulVec, dotProduct, Fin.sum_univ_three] using e0 2 (by decide),
    by simpa [mulVec, dotProduct, Fin.sum_univ_three] using e1 2 (by decide)⟩

instance : DecidablePred cond1 := fun g => by unfold cond1; infer_instance
instance : DecidablePred cond2 := fun g => by unfold cond2; infer_instance
instance : DecidablePred condB := fun g => by unfold condB; infer_instance

theorem card_SL3 : Nat.card SL3 = 168 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem card_cond1 : Nat.card {g : SL3 // cond1 g} = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_cond2 : Nat.card {g : SL3 // cond2 g} = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem card_condB : Nat.card {g : SL3 // condB g} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem exp_cond1 : ∀ z : SL3, cond1 z → z ^ 3 = 1 ∨ z ^ 4 = 1 := by decide +kernel
theorem exp_cond2 : ∀ z : SL3, cond2 z → z ^ 3 = 1 ∨ z ^ 4 = 1 := by decide +kernel

def odd1 : Finset SL3 := Finset.univ.filter fun z => cond1 z ∧ z ^ 3 = 1

def odd2 : Finset SL3 := Finset.univ.filter fun z => cond2 z ∧ z ^ 3 = 1

def borelElts : Finset SL3 := Finset.univ.filter fun z => condB z

theorem witness1_fin : ∀ z ∈ odd1, ∃ z₁ ∈ odd1, ∃ z₂ ∈ odd1, ∃ b₁ ∈ borelElts, ∃ b₂ ∈ borelElts,
    z = z₁ * b₁ * z₁⁻¹ * b₁⁻¹ * (z₂ * b₂ * z₂⁻¹ * b₂⁻¹) := by decide +kernel

theorem witness2_fin : ∀ z ∈ odd2, ∃ z₁ ∈ odd2, ∃ z₂ ∈ odd2, ∃ b₁ ∈ borelElts, ∃ b₂ ∈ borelElts,
    z = z₁ * b₁ * z₁⁻¹ * b₁⁻¹ * (z₂ * b₂ * z₂⁻¹ * b₂⁻¹) := by decide +kernel

theorem witness1 : ∀ z : SL3, cond1 z → z ^ 3 = 1 →
    ∃ z₁ z₂ b₁ b₂ : SL3, cond1 z₁ ∧ z₁ ^ 3 = 1 ∧ cond1 z₂ ∧ z₂ ^ 3 = 1 ∧ condB b₁ ∧ condB b₂ ∧
      z = z₁ * b₁ * z₁⁻¹ * b₁⁻¹ * (z₂ * b₂ * z₂⁻¹ * b₂⁻¹) := by
  intro z hz hz3
  obtain ⟨z₁, h₁, z₂, h₂, b₁, hb₁, b₂, hb₂, h⟩ :=
    witness1_fin z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, hz3⟩)
  simp only [odd1, borelElts, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂ hb₁ hb₂
  exact ⟨z₁, z₂, b₁, b₂, h₁.1, h₁.2, h₂.1, h₂.2, hb₁, hb₂, h⟩

theorem witness2 : ∀ z : SL3, cond2 z → z ^ 3 = 1 →
    ∃ z₁ z₂ b₁ b₂ : SL3, cond2 z₁ ∧ z₁ ^ 3 = 1 ∧ cond2 z₂ ∧ z₂ ^ 3 = 1 ∧ condB b₁ ∧ condB b₂ ∧
      z = z₁ * b₁ * z₁⁻¹ * b₁⁻¹ * (z₂ * b₂ * z₂⁻¹ * b₂⁻¹) := by
  intro z hz hz3
  obtain ⟨z₁, h₁, z₂, h₂, b₁, hb₁, b₂, hb₂, h⟩ :=
    witness2_fin z (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz, hz3⟩)
  simp only [odd2, borelElts, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂ hb₁ hb₂
  exact ⟨z₁, z₂, b₁, b₂, h₁.1, h₁.2, h₂.1, h₂.2, hb₁, hb₂, h⟩

end SBd3

end CFSG.Quasithin
