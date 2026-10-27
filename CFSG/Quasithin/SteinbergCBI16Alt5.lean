module

public import CFSG.Quasithin.SteinbergCBI16Coords
public import CFSG.Quasithin.SteinbergCBI16Dn
public import CFSG.Quasithin.SteinbergCBI16Gen

public section

namespace CFSG.Quasithin.SteinbergCB.I16

open Equiv CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB.G2Two

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def coords5 : DnCoords 5 4 :=
  DnCoords.ofCodes (projOdd 4) (inclOdd 4) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) fun h => absurd h (by decide)

@[expose] def a5 : Perm (Fin 5) := swap 0 1 * swap 1 2

@[expose] def b5 : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

theorem a5_mem : a5 ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup, a5]
  decide +kernel

theorem b5_mem : b5 ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup, b5]
  decide +kernel

@[expose] def gens5 : Fin 2 → ↥(alternatingGroup (Fin 5)) := ![⟨a5, a5_mem⟩, ⟨b5, b5_mem⟩]

@[expose] def trans5 : List (List (List (Fin 2))) :=
  [[[], [0], [0, 0], [1, 0, 0], [1, 1, 0, 0]], [[], [1, 0, 1, 1, 1, 0], [0, 1, 0],
    [0, 0, 1, 0, 1, 0]], [[], [0, 0, 1], [1, 1, 1, 1, 0]]]

theorem closure_gens5 : Subgroup.closure (Set.range gens5) = ⊤ :=
  closure_eq_top_of_transversals (by norm_num) gens5
    (fun j y => (trans5.getD j []).getD (y - j) []) (by decide +kernel)

@[expose] def cols5 : List (List ℕ) := [[2, 4, 1, 8], [3, 5, 9, 1]]

@[expose] def rels5 : List (List (Fin 2)) := [[0, 0, 0], [0, 1, 1, 0, 1, 1]]

theorem cols5_lt : ∀ i : Fin 2, ∀ c ∈ cols5.getD i [], c < 2 ^ 4 := by
  decide +kernel

theorem act5 : ∀ i : Fin 2, ∀ x < 2 ^ 4,
    coords5.actA (gens5 i) (toV 4 x) = toV 4 (mApp (cols5.getD i []) x) := by
  decide +kernel

theorem rels5_perm : ∀ r ∈ rels5, wordEval (fun i => (gens5 i : Perm (Fin 5))) r = 1 := by
  decide +kernel

theorem rels5_eq : ∀ r ∈ rels5, wordEval gens5 r = 1 := fun r hr =>
  Subtype.ext ((val_wordEval gens5 r).trans (rels5_perm r hr))

theorem class5 : ∀ v₀ < 2 ^ 4, ∀ v₁ < 2 ^ 4, (∀ r ∈ rels5, foxCode cols5 [v₀, v₁] r = 0) →
    ∃ x < 2 ^ 4, ∃ ε < 2, v₀ = mApp (cols5.getD 0 []) x ^^^ x ^^^ ε * [0, 0].getD 0 0 ∧
      v₁ = mApp (cols5.getD 1 []) x ^^^ x ^^^ ε * [0, 0].getD 1 0 := by
  decide +kernel

theorem Z1A_le_B1A_5 : Z1A coords5.actA ≤ B1A coords5.actA := by
  intro f hf
  have h0 : ∀ i : Fin 2, (0 : ↥(alternatingGroup (Fin 5)) → Fin 4 → ZMod 2) (gens5 i) =
      toV 4 ([0, 0].getD i 0) := by
    intro i
    fin_cases i <;> exact (toV_zero 4).symm
  rcases classify_Z1A closure_gens5 cols5_lt act5 rels5_eq (zero_mem _) h0 class5 f hf with h | h
  · exact h
  · rwa [sub_zero] at h

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_alternatingNatural_five {ρ : Representation (ZMod 2) Γ W}
    (h : Explicit.AlternatingNatural ρ 5 .alternating) : Module.finrank (ZMod 2) (H1 ρ) = 0 :=
  coords5.finrank_H1_eq_zero h Z1A_le_B1A_5

end CFSG.Quasithin.SteinbergCB.I16
