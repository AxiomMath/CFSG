
module

public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.ThSchreier.LocalDataBase
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

@[expose] public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.ThSchreier TauCeti Pointwise

noncomputable abbrev P : Type := SporadicName.Th.Group

noncomputable abbrev gen (i : ℕ) : P := presGen SporadicName.Th.presentation i

noncomputable def K : Subgroup P := Subgroup.closure (Set.range fun i : Fin 7 => gen i)

noncomputable abbrev Wset : Set RowV := (planeW : Set RowV)

noncomputable def stabK (v : P) : Subgroup P := K ⊓ K.map (MulAut.conj v).toMonoidHom

def mD : Fin 11 → ℕ := ![1, 54, 126, 6, 72, 78, 486, 13824, 288, 3528, 36864]

def nD : Fin 11 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 19, 3, 0, 51]

def thOrder : ℕ := 90745943887872000

def DceFacts : Prop :=
  Nat.card P = thOrder → ∃ v : Fin 11 → P, v 0 = 1 ∧
    (∀ g : P, ∃ D, ∃ k ∈ K, ∃ k' ∈ K, g = k * v D * k') ∧
    (∀ D, mD D ≤ Nat.card (stabK (v D))) ∧
    (∀ D, D ≠ 0 → Nat.card {k : P // k ∈ stabK (v D) ∧ ∃ g ∈ K, g * gen 0 * g⁻¹ = k} ≤ nD D) ∧
    Nat.card K ≤ 634023936 ∧
    819 ≤ Nat.card {k : P // ∃ g ∈ K, g * gen 0 * g⁻¹ = k} ∧
    69615 ≤ Nat.card {k : P // k ∈ K ∧ orderOf k = 2} ∧
    (∀ s ∈ stabK (v 3), (gen 1)⁻¹ * s * gen 1 ∈ stabK (v 3) → s = 1)

def fusionWord0' : List ℕ := [1, 2, 2, 1, 2]

def fusionWord1' : List ℕ := [2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2]

end CFSG.Sporadic.Th.Kernel
