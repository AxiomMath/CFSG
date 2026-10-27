module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Core

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P55

variable {ℓ : Line Γ} {u : G}

theorem core_exists {tL tR : ℤ} (hfin : ∀ j, j ∈ ℓ.fixIdx u ↔ tL ≤ j ∧ j ≤ tR) {i₀ : ℤ}
    (hi₀ : u ∈ Cen (ℓ.edgeCirc (G := G) i₀)) :
    ∃ a b : ℤ, ℓ.IsCoreC u a b ∧ a ≤ i₀ ∧ i₀ < b := by
  classical
  have hS : ∀ i, u ∈ Cen (ℓ.edgeCirc (G := G) i) → tL ≤ i ∧ i + 1 ≤ tR := by
    intro i hi
    have hf := ℓ.edgeCirc_fix hi.1
    have h0 := (hfin i).1 hf.1
    have h1 := (hfin (i + 1)).1 hf.2
    omega
  obtain ⟨a, ⟨ha1, ha2⟩, ha3⟩ := Int.exists_least_of_bdd
    (P := fun a₀ => a₀ ≤ i₀ ∧ ∀ i, a₀ ≤ i → i ≤ i₀ → u ∈ Cen (ℓ.edgeCirc (G := G) i))
    ⟨tL, fun a₀ ha₀ => (hS a₀ (ha₀.2 a₀ le_rfl ha₀.1)).1⟩
    ⟨i₀, le_rfl, fun i h1 h2 => by rwa [le_antisymm h2 h1]⟩
  obtain ⟨b, ⟨hb1, hb2⟩, hb3⟩ := Int.exists_greatest_of_bdd
    (P := fun b₀ => i₀ < b₀ ∧ ∀ i, i₀ ≤ i → i < b₀ → u ∈ Cen (ℓ.edgeCirc (G := G) i))
    ⟨tR, fun b₀ hb₀ => by
      have := hS (b₀ - 1) (hb₀.2 (b₀ - 1) (by have := hb₀.1; omega) (by omega))
      omega⟩
    ⟨i₀ + 1, by omega, fun i h1 h2 => by rwa [show i = i₀ by omega]⟩
  have hP : ∀ i, a ≤ i → i < b → u ∈ Cen (ℓ.edgeCirc (G := G) i) := fun i h1 h2 => by
    rcases le_total i i₀ with h | h
    · exact ha2 i h1 h
    · exact hb2 i h h2
  refine ⟨a, b, ⟨by omega, fun i h1 h2 => ?_, hP, ?_, ?_⟩, ha1, hb1⟩
  · rcases lt_or_eq_of_le h2 with h | h
    · exact P55.fixIdx_of_cen (hP i h1 h)
    · have hf := ℓ.edgeCirc_fix (hP (b - 1) (by omega) (by omega)).1
      rw [sub_add_cancel] at hf
      rw [h]
      exact hf.2
  · rintro ⟨-, h⟩
    have := ha3 (a - 1) ⟨by omega, fun i h1 h2 => by
      rcases lt_or_eq_of_le h1 with h' | h'
      · exact ha2 i (by omega) h2
      · rwa [← h']⟩
    omega
  · rintro ⟨-, h⟩
    have := hb3 (b + 1) ⟨by omega, fun i h1 h2 => by
      rcases lt_or_eq_of_le (Int.lt_add_one_iff.1 h2) with h' | h'
      · exact hb2 i h1 h'
      · rwa [h']⟩
    omega

end P55

end CFSG.Quasithin.Fan86
