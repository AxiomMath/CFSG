module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeCentralizer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryRegular
  CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

variable {ℓ f n p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)

@[expose] noncomputable def idSpecialBlock (x : gramSU h (idGram K n)) (a : K[X]) :
    Subgroup (primeFormUnitary h (idGram K n)) :=
  (specialBlock (idForm h n) (toLinU h n (liftUnitary x)) a).comap (toLinU h n)

@[expose] noncomputable def idBlockImage (x : gramSU h (idGram K n)) (a : K[X]) :
    Subgroup (MulAut (primeFormP h (idGram K n))) :=
  (idSpecialBlock h x a).map (primeFormConjHom h (idGram K n))

@[expose] noncomputable def idCenterUnits (x : gramSU h (idGram K n)) :
    Subgroup (primeFormUnitary h (idGram K n)) :=
  (centerUnitary (idForm h n) (toLinU h n (liftUnitary x))).comap (toLinU h n)

variable {h}

theorem mem_idSpecialBlock {x : gramSU h (idGram K n)} {a : K[X]}
    {A : primeFormUnitary h (idGram K n)} :
    A ∈ idSpecialBlock h x a ↔
      toLinU h n A ∈ specialBlock (idForm h n) (toLinU h n (liftUnitary x)) a := Iff.rfl

theorem mem_idCenterUnits {x : gramSU h (idGram K n)} {A : primeFormUnitary h (idGram K n)} :
    A ∈ idCenterUnits h x ↔
      toLinU h n A ∈ centerUnitary (idForm h n) (toLinU h n (liftUnitary x)) := Iff.rfl

theorem range_toLinU : (toLinU h n).range = sesqUnitaryGroup (idForm h n) := by
  ext g
  constructor
  · rintro ⟨A, rfl⟩
    exact toLinU_mem A
  · intro hg
    exact exists_toLinU hg

namespace LiftData

variable {x : gramSU h (idGram K n)} (L : LiftData h n p x)

include L in
theorem primaryData : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n (liftUnitary x)) :=
  ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n, toLinU_mem _, L.squarefree_minpoly⟩

end LiftData

theorem map_gramSU_eq_range_conj :
    ((gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n))).map
        (primeFormConjHom h (idGram K n)) =
      (MulAut.conj : primeFormP h (idGram K n) →*
        MulAut (primeFormP h (idGram K n))).range := by
  ext α
  rw [mem_inner_iff]
  constructor
  · rintro ⟨A, hA, rfl⟩
    exact ⟨⟨A, hA⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, s.2.1⟩, s.2, rfl⟩

theorem mem_centralizer_iff_toLinU (x : gramSU h (idGram K n))
    (A : primeFormUnitary h (idGram K n)) :
    A ∈ Subgroup.centralizer ({liftUnitary x} : Set (primeFormUnitary h (idGram K n))) ↔
      toLinU h n A ∈ unitaryCentralizer (idForm h n) (toLinU h n (liftUnitary x)) := by
  rw [centralizer_eq_comap_unitaryCentralizer x]
  rfl

theorem idSpecialBlock_le (x : gramSU h (idGram K n)) (a : K[X]) :
    idSpecialBlock h x a ≤ Subgroup.centralizer ({liftUnitary x} : Set _) := by
  intro A hA
  exact (mem_centralizer_iff_toLinU x A).mpr (specialBlock_le_unitaryCentralizer hA)

theorem specialBlock_le_range (x : gramSU h (idGram K n)) (a : K[X]) :
    specialBlock (idForm h n) (toLinU h n (liftUnitary x)) a ≤ (toLinU h n).range := by
  rw [range_toLinU]
  exact specialBlock_le_unitaryCentralizer.trans (fun g hg => hg.1)

theorem map_toLinU_idSpecialBlock (x : gramSU h (idGram K n)) (a : K[X]) :
    (idSpecialBlock h x a).map (toLinU h n) =
      specialBlock (idForm h n) (toLinU h n (liftUnitary x)) a := by
  unfold idSpecialBlock
  rw [Subgroup.map_comap_eq]
  exact inf_of_le_right (specialBlock_le_range x a)

end CFSG.RankThree.PartOne.KCUnitaryModel
