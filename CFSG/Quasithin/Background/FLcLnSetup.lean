module

public import CFSG.Quasithin.Background.FLcLn

public section

namespace CFSG.Quasithin.FLc

open CFSG.Quasithin CFSG.QuasithinUnique

variable {A : Type} [Group A]

theorem ln_setup [Finite A] {L X S P₀ : Subgroup A} {n : ℕ} (hn : 1 ≤ n) (iso : ↥L ≃* SLt n)
    (hLX : L ≤ X) (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L) (hS : IsSylowTwoOf S X)
    (hpar : IsMinParabolicOf L P₀) (hP₀n : ∀ s ∈ S, ∀ p ∈ P₀, s * p * s⁻¹ ∈ P₀) :
    ∃ D : BorelIso n L (S ⊓ L), S ⊓ L ≤ P₀ ∧ P₀ ≤ L ∧ ∃ x₀, IsNode n x₀ ∧ x₀ ∉ D.cutsOf P₀ ∧
      ∀ y, IsNode n y → y ∉ D.cutsOf P₀ → y = x₀ := by
  have hXn : X ≤ Subgroup.normalizer (L : Set A) := le_normalizer_of_conj_mem hLn
  have hBL : IsSylowTwoOf (S ⊓ L) L := B6.isSylowTwoOf_inf_normal hS hLX hXn
  obtain ⟨D⟩ := exists_borelIso hn hBL iso
  have hBN₀ : S ⊓ L ≤ Subgroup.normalizer (P₀ : Set A) :=
    inf_le_left.trans (le_normalizer_of_conj_mem' hP₀n)
  obtain ⟨hBP₀, hP₀L, hunique⟩ := minParabolic_transfer hpar hBL hBN₀
  obtain ⟨x₀, hx₀, hx₀P, hx₀u⟩ := D.exists_unique_node_of_unique_max hBL.1 hBP₀ hP₀L hunique
  exact ⟨D, hBP₀.le, hP₀L, x₀, hx₀, hx₀P, hx₀u⟩

theorem exists_two_nodes {n : ℕ} (x : ℕ) (hn : 4 ≤ n) :
    ∃ i j, IsNode n i ∧ IsNode n j ∧ i ≠ j ∧ i ≠ x ∧ j ≠ x := by
  by_cases h1 : x = 1
  · exact ⟨2, 3, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega, by omega⟩
  · by_cases h2 : x = 2
    · exact ⟨1, 3, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega, by omega⟩
    · exact ⟨1, 2, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega, by omega, by omega⟩

end CFSG.Quasithin.FLc
