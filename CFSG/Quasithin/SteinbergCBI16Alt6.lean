module

public import CFSG.Quasithin.SteinbergCBI16Coords
public import CFSG.Quasithin.SteinbergCBI16Dn
public import CFSG.Quasithin.SteinbergCBI16Gen

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open Equiv CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB.G2Two

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def coords6 : DnCoords 6 4 :=
  DnCoords.ofCodes (projEven 4) (inclEven 4) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) fun _ => by decide +kernel

@[expose] def a6 : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def b6 : Perm (Fin 6) := swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5

theorem a6_mem : a6 ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup, a6]
  decide +kernel

theorem b6_mem : b6 ∈ alternatingGroup (Fin 6) := by
  rw [Perm.mem_alternatingGroup, b6]
  decide +kernel

@[expose] def gens6 : Fin 2 → ↥(alternatingGroup (Fin 6)) := ![⟨a6, a6_mem⟩, ⟨b6, b6_mem⟩]

@[expose] def trans6 : List (List (List (Fin 2))) :=
  [[[], [0], [0, 0], [1, 0, 0], [1, 1, 0, 0], [1, 1, 1, 0, 0]],
   [[], [1], [1, 1], [1, 1, 1], [1, 1, 1, 1]],
   [[], [1, 0, 1, 0, 1, 1, 1], [0, 1, 0, 1], [1, 1, 0, 1, 0, 0, 1, 0]],
   [[], [1, 1, 0, 1, 0, 1, 1], [1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1]]]

theorem closure_gens6 : Subgroup.closure (Set.range gens6) = ⊤ :=
  closure_eq_top_of_transversals (by norm_num) gens6
    (fun j y => (trans6.getD j []).getD (y - j) []) (by decide +kernel)

@[expose] def cols6 : List (List ℕ) := [[2, 4, 1, 8], [14, 11, 7, 15]]

@[expose] def rels6 : List (List (Fin 2)) :=
  [[0, 0, 0], [0, 1, 0, 1, 0, 1, 0, 1]]

theorem cols6_lt : ∀ i : Fin 2, ∀ c ∈ cols6.getD i [], c < 2 ^ 4 := by
  decide +kernel

theorem act6 : ∀ i : Fin 2, ∀ x < 2 ^ 4,
    coords6.actA (gens6 i) (toV 4 x) = toV 4 (mApp (cols6.getD i []) x) := by
  decide +kernel

theorem rels6_perm : ∀ r ∈ rels6, wordEval (fun i => (gens6 i : Perm (Fin 6))) r = 1 := by
  decide +kernel

theorem rels6_eq : ∀ r ∈ rels6, wordEval gens6 r = 1 := fun r hr =>
  Subtype.ext ((val_wordEval gens6 r).trans (rels6_perm r hr))

theorem class6 : ∀ v₀ < 2 ^ 4, ∀ v₁ < 2 ^ 4, (∀ r ∈ rels6, foxCode cols6 [v₀, v₁] r = 0) →
    ∃ x < 2 ^ 4, ∃ ε < 2, v₀ = mApp (cols6.getD 0 []) x ^^^ x ^^^ ε * [3, 0].getD 0 0 ∧
      v₁ = mApp (cols6.getD 1 []) x ^^^ x ^^^ ε * [3, 0].getD 1 0 := by
  decide +kernel

theorem f0_gens6 : ∀ i : Fin 2,
    coords6.f0 0 (gens6 i : Perm (Fin 6)) = toV 4 ([3, 0].getD i 0) := by
  decide +kernel

theorem no6 : ∀ x < 2 ^ 4, ¬([3, 0].getD 0 0 = mApp (cols6.getD 0 []) x ^^^ x ∧
    [3, 0].getD 1 0 = mApp (cols6.getD 1 []) x ^^^ x) := by
  decide +kernel

theorem card_Z1A_6 : Nat.card (Z1A coords6.actA) = 2 * Nat.card (B1A coords6.actA) :=
  card_Z1A_eq_two_mul vec_add_self (coords6.f0_mem 0)
    (not_mem_B1A_of_codes cols6_lt act6 (by decide) f0_gens6 no6)
    (classify_Z1A closure_gens6 cols6_lt act6 rels6_eq (coords6.f0_mem 0) f0_gens6 class6)

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_alternatingNatural_six {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.AlternatingNatural ρ 6 .alternating) : Module.finrank (ZMod 2) (H1 ρ) = 1 :=
  coords6.finrank_H1_eq_one h card_Z1A_6

end CFSG.Quasithin.SteinbergCB.I16
