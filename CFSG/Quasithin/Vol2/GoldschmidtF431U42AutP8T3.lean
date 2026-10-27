module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8T0

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

section Gen

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}
variable (c : AutCtx G M₁ M₂ z)

theorem ncard_le_of_idx (S : Set G) (g : G) (L : List ℕ) (hL : L.Nodup)
    (hS : ∀ x ∈ S, ∃ j ∈ L, ivG c j = g * x * g⁻¹) : S.ncard ≤ L.length := by
  classical
  choose! φ hφ using hS
  have hmap : ∀ x ∈ S, φ x ∈ (↑L.toFinset : Set ℕ) := fun x hx => by
    simpa using (hφ x hx).1
  have hinj : Set.InjOn φ S := by
    intro x hx y hy hxy
    have h1 := (hφ x hx).2
    have h2 := (hφ y hy).2
    rw [hxy, h2] at h1
    have h3 : g * x * g⁻¹ = g * y * g⁻¹ := h1.symm
    simpa using h3
  have := Set.ncard_le_ncard_of_injOn φ hmap hinj (Set.toFinite _)
  rwa [Set.ncard_coe_finset, List.toFinset_card_of_nodup hL] at this

theorem le_ncard_of_idx (S : Set G) (g : G) (L : List ℕ) (hL : L.Nodup) (hk : ∀ j ∈ L, j < 43)
    (hS : ∀ j ∈ L, g⁻¹ * ivG c j * g ∈ S) : L.length ≤ S.ncard := by
  classical
  have hinj : Set.InjOn (fun j : ℕ => g⁻¹ * ivG c j * g) (↑L.toFinset : Set ℕ) := by
    intro j hj j' hj' h
    have hj1 : j ∈ L := by simpa using hj
    have hj2 : j' ∈ L := by simpa using hj'
    have h1 : ivG c j = ivG c j' := by simpa using h
    exact ivG_inj c (hk j hj1) (hk j' hj2) h1
  have hmap : ∀ j ∈ (↑L.toFinset : Set ℕ), (fun j : ℕ => g⁻¹ * ivG c j * g) j ∈ S := by
    intro j hj
    exact hS j (by simpa using hj)
  have := Set.ncard_le_ncard_of_injOn _ hmap hinj (Set.toFinite _)
  rwa [Set.ncard_coe_finset, List.toFinset_card_of_nodup hL] at this

end Gen

end CFSG.Quasithin.H13.F431.U42Aut
