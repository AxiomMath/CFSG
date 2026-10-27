module

public import CFSG.Quasithin.SteinbergCBI16Coords
public import CFSG.Quasithin.SteinbergCBI16Dn
public import CFSG.Quasithin.SteinbergCBI16Gen

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open Equiv CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB.G2Two

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def coords8 : DnCoords 8 6 :=
  DnCoords.ofCodes (projEven 6) (inclEven 6) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) fun _ => by decide +kernel

@[expose] def a8 : Perm (Fin 8) := swap 0 1 * swap 1 2

@[expose] def b8 : Perm (Fin 8) := swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6 * swap 6 7

theorem a8_mem : a8 ∈ alternatingGroup (Fin 8) := by
  rw [Perm.mem_alternatingGroup, a8]
  decide +kernel

theorem b8_mem : b8 ∈ alternatingGroup (Fin 8) := by
  rw [Perm.mem_alternatingGroup, b8]
  decide +kernel

@[expose] def gens8 : Fin 2 → ↥(alternatingGroup (Fin 8)) := ![⟨a8, a8_mem⟩, ⟨b8, b8_mem⟩]

@[expose] def trans8 : List (List (List (Fin 2))) :=
  [[[], [0], [0, 0], [1, 0, 0], [1, 1, 0, 0], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0, 0],
    [1, 1, 1, 1, 1, 0, 0]],
   [[], [1], [1, 1], [1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 1]],
   [[], [1, 0, 1, 0, 1, 1, 1, 1, 1], [0, 1, 0, 1], [0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0],
    [0, 1, 0, 1, 0, 1, 0, 1], [1, 1, 1, 1, 0, 1, 0, 0, 1, 0]],
   [[], [1, 1, 0, 1, 0, 1, 1, 1, 1], [1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]],
   [[], [1, 1, 1, 0, 1, 0, 1, 1, 1], [0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1],
    [0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1]],
   [[], [1, 1, 1, 1, 0, 1, 0, 1, 1], [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1]]]

theorem closure_gens8 : Subgroup.closure (Set.range gens8) = ⊤ :=
  closure_eq_top_of_transversals (by norm_num) gens8
    (fun j y => (trans8.getD j []).getD (y - j) []) (by decide +kernel)

@[expose] def cols8 : List (List ℕ) := [[2, 4, 1, 8, 16, 32], [62, 59, 55, 47, 31, 63]]

@[expose] def rels8 : List (List (Fin 2)) :=
  [[0, 0, 0], [0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1]]

theorem cols8_lt : ∀ i : Fin 2, ∀ c ∈ cols8.getD i [], c < 2 ^ 6 := by
  decide +kernel

theorem act8 : ∀ i : Fin 2, ∀ x < 2 ^ 6,
    coords8.actA (gens8 i) (toV 6 x) = toV 6 (mApp (cols8.getD i []) x) := by
  decide +kernel

theorem rels8_perm : ∀ r ∈ rels8, wordEval (fun i => (gens8 i : Perm (Fin 8))) r = 1 := by
  decide +kernel

theorem rels8_eq : ∀ r ∈ rels8, wordEval gens8 r = 1 := fun r hr =>
  Subtype.ext ((val_wordEval gens8 r).trans (rels8_perm r hr))

theorem class8 : ∀ v₀ < 2 ^ 6, ∀ v₁ < 2 ^ 6, (∀ r ∈ rels8, foxCode cols8 [v₀, v₁] r = 0) →
    ∃ x < 2 ^ 6, ∃ ε < 2, v₀ = mApp (cols8.getD 0 []) x ^^^ x ^^^ ε * [3, 0].getD 0 0 ∧
      v₁ = mApp (cols8.getD 1 []) x ^^^ x ^^^ ε * [3, 0].getD 1 0 := by
  decide +kernel

theorem f0_gens8 : ∀ i : Fin 2,
    coords8.f0 0 (gens8 i : Perm (Fin 8)) = toV 6 ([3, 0].getD i 0) := by
  decide +kernel

theorem no8 : ∀ x < 2 ^ 6, ¬([3, 0].getD 0 0 = mApp (cols8.getD 0 []) x ^^^ x ∧
    [3, 0].getD 1 0 = mApp (cols8.getD 1 []) x ^^^ x) := by
  decide +kernel

theorem card_Z1A_8 : Nat.card (Z1A coords8.actA) = 2 * Nat.card (B1A coords8.actA) :=
  card_Z1A_eq_two_mul vec_add_self (coords8.f0_mem 0)
    (not_mem_B1A_of_codes cols8_lt act8 (by decide) f0_gens8 no8)
    (classify_Z1A closure_gens8 cols8_lt act8 rels8_eq (coords8.f0_mem 0) f0_gens8 class8)

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_alternatingNatural_eight {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.AlternatingNatural ρ 8 .alternating) : Module.finrank (ZMod 2) (H1 ρ) = 1 :=
  coords8.finrank_H1_eq_one h card_Z1A_8

end CFSG.Quasithin.SteinbergCB.I16
