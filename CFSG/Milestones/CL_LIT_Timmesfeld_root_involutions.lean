module

public import CFSG.Timmesfeld.Assembly

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.cl_lit_timmesfeld_root_involutions
    (G : Type) [Group G] [Finite G] (D : Set G)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hgen : Subgroup.closure D = ⊤)
    (hcenter : Subgroup.center G = ⊥)
    (hodd : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (hprod : ∀ d ∈ D, ∀ e ∈ D,
      orderOf (d * e) = 2 ∨ orderOf (d * e) = 4 ∨ Odd (orderOf (d * e)))
    (hfour : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D)
    (hnondeg : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) :
    IsSimpleGroup G ∧
      ((Nat.card G ∈ lieOrdersChar 2 ∧
          (∀ n f : ℕ, 2 ≤ n → 1 ≤ f → Nat.card G ≠ ordTwistedA n (2 ^ f)) ∧
          (∀ f : ℕ, 1 ≤ f → Nat.card G ≠ ordBC 2 (2 ^ f))) ∨
        Nonempty (G ≃* PSU3 3 1) ∨
        Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
        Nat.card G = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7) := by
  have _hcenter := hcenter
  exact (CFSG.Timmesfeld.conclusions G D hclass hinv hgen hodd hO2 hprod hfour hnondeg).1

end CFSG.Open

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.cl_lit_timmesfeld_root_involutions_models
    (G : Type) [Group G] [Finite G] (D : Set G)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hgen : Subgroup.closure D = ⊤)
    (hcenter : Subgroup.center G = ⊥)
    (hodd : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (hprod : ∀ d ∈ D, ∀ e ∈ D,
      orderOf (d * e) = 2 ∨ orderOf (d * e) = 4 ∨ Odd (orderOf (d * e)))
    (hfour : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D)
    (hnondeg : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) :
    (Blueprint.EvenLieType G ∧
      (∀ n f : ℕ, 3 ≤ n → 1 ≤ f → ¬ Blueprint.LieModel G .PSU n 2 f) ∧
      (∀ f : ℕ, 1 ≤ f → ¬ Blueprint.LieModel G .PSp 2 2 f)) ∨
    Blueprint.LieModel G .PSU 3 3 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
      Blueprint.NativeSporadic.IsSporadic G .J2 := by
  have _hcenter := hcenter
  exact (CFSG.Timmesfeld.conclusions G D hclass hinv hgen hodd hO2 hprod hfour hnondeg).2

end CFSG.Open
