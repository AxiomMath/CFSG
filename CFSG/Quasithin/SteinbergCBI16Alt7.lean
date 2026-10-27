module

public import CFSG.Quasithin.SteinbergCBI16Coords
public import CFSG.Quasithin.SteinbergCBI16Dn
public import CFSG.Quasithin.SteinbergCBI16Gen

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open Equiv CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB.G2Two

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def coords7 : DnCoords 7 6 :=
  DnCoords.ofCodes (projOdd 6) (inclOdd 6) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) fun h => absurd h (by decide)

@[expose] def a7 : Perm (Fin 7) := swap 0 1 * swap 1 2

@[expose] def b7 : Perm (Fin 7) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6

theorem a7_mem : a7 ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup, a7]
  decide +kernel

theorem b7_mem : b7 ∈ alternatingGroup (Fin 7) := by
  rw [Perm.mem_alternatingGroup, b7]
  decide +kernel

@[expose] def gens7 : Fin 2 → ↥(alternatingGroup (Fin 7)) := ![⟨a7, a7_mem⟩, ⟨b7, b7_mem⟩]

@[expose] def trans7 : List (List (List (Fin 2))) :=
  [[[], [0], [0, 0], [1, 0, 0], [1, 1, 0, 0], [1, 1, 1, 0, 0], [1, 1, 1, 1, 0, 0]],
   [[], [1, 0, 1, 1, 1, 1, 1, 0], [0, 1, 0], [0, 0, 1, 0, 1, 0], [0, 1, 1, 0, 1, 0],
    [1, 1, 1, 1, 0, 1, 0, 0]],
   [[], [0, 0, 1], [0, 0, 1, 0, 0, 1], [0, 0, 1, 0, 0, 1, 0, 0, 1], [1, 1, 1, 1, 1, 1, 0]],
   [[], [1, 1, 1, 0, 1, 1, 1, 1], [1, 1, 1, 0, 0, 1, 1, 1, 1],
    [1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1]],
   [[], [1, 1, 1, 1, 0, 1, 1, 1], [1, 1, 1, 1, 0, 0, 1, 1, 1]]]

theorem closure_gens7 : Subgroup.closure (Set.range gens7) = ⊤ :=
  closure_eq_top_of_transversals (by norm_num) gens7
    (fun j y => (trans7.getD j []).getD (y - j) []) (by decide +kernel)

@[expose] def cols7 : List (List ℕ) := [[2, 4, 1, 8, 16, 32], [3, 5, 9, 17, 33, 1]]

@[expose] def rels7 : List (List (Fin 2)) :=
  [[0, 0, 0], [0, 1, 1, 0, 1, 1, 0, 1, 1]]

theorem cols7_lt : ∀ i : Fin 2, ∀ c ∈ cols7.getD i [], c < 2 ^ 6 := by
  decide +kernel

theorem act7 : ∀ i : Fin 2, ∀ x < 2 ^ 6,
    coords7.actA (gens7 i) (toV 6 x) = toV 6 (mApp (cols7.getD i []) x) := by
  decide +kernel

theorem rels7_perm : ∀ r ∈ rels7, wordEval (fun i => (gens7 i : Perm (Fin 7))) r = 1 := by
  decide +kernel

theorem rels7_eq : ∀ r ∈ rels7, wordEval gens7 r = 1 := fun r hr =>
  Subtype.ext ((val_wordEval gens7 r).trans (rels7_perm r hr))

theorem class7 : ∀ v₀ < 2 ^ 6, ∀ v₁ < 2 ^ 6, (∀ r ∈ rels7, foxCode cols7 [v₀, v₁] r = 0) →
    ∃ x < 2 ^ 6, ∃ ε < 2, v₀ = mApp (cols7.getD 0 []) x ^^^ x ^^^ ε * [0, 0].getD 0 0 ∧
      v₁ = mApp (cols7.getD 1 []) x ^^^ x ^^^ ε * [0, 0].getD 1 0 := by
  decide +kernel

theorem Z1A_le_B1A_7 : Z1A coords7.actA ≤ B1A coords7.actA := by
  intro f hf
  have h0 : ∀ i : Fin 2, (0 : ↥(alternatingGroup (Fin 7)) → Fin 6 → ZMod 2) (gens7 i) =
      toV 6 ([0, 0].getD i 0) := by
    intro i
    fin_cases i <;> exact (toV_zero 6).symm
  rcases classify_Z1A closure_gens7 cols7_lt act7 rels7_eq (zero_mem _) h0 class7 f hf with
    h | h
  · exact h
  · rwa [sub_zero] at h

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_alternatingNatural_seven {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.AlternatingNatural ρ 7 .alternating) : Module.finrank (ZMod 2) (H1 ρ) = 0 :=
  coords7.finrank_H1_eq_zero h Z1A_le_B1A_7

end CFSG.Quasithin.SteinbergCB.I16
