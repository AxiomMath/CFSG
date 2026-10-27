module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small

open Subgroup

theorem centralizer_singleton_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    centralizer ({e x} : Set H) = (centralizer ({x} : Set G)).map e.toMonoidHom := by
  ext h
  constructor
  · intro hh
    refine ⟨e.symm h, ?_, e.apply_symm_apply h⟩
    show e.symm h ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have := (mem_centralizer_iff.mp hh) (e g) (by simp)
    apply e.injective
    simpa using this
  · rintro ⟨g, hg, rfl⟩
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := (mem_centralizer_iff.mp hg) x (by simp)
    show e x * e g = e g * e x
    rw [← map_mul, ← map_mul, this]

theorem card_centralizer_singleton_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (x : G) : Nat.card (centralizer ({e x} : Set H)) = Nat.card (centralizer ({x} : Set G)) := by
  rw [centralizer_singleton_mulEquiv, Subgroup.card_map_of_injective e.injective]

theorem isCyclic_centralizer_singleton_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (x : G) (h : IsCyclic (centralizer ({x} : Set G))) :
    IsCyclic (centralizer ({e x} : Set H)) := by
  rw [centralizer_singleton_mulEquiv]
  exact isCyclic_of_surjective (e.toMonoidHom.subgroupMap (centralizer ({x} : Set G)))
    (MonoidHom.subgroupMap_surjective _ _)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Small
