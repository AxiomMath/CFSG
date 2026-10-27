module

public import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec8.Hering611SGenB

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open scoped Bracket

variable {G : Type} [Group G] [Finite G]

private theorem glueB_conj_mem {W : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) {w : G} (hw : w ∈ W) : x * w * x⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.mp hx w).mp hw

private def glueB_commSub (U : Subgroup G) {V X : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) : Subgroup G where
  carrier := {x | x ∈ X ∧ ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ V}
  one_mem' := by
    show (1 : G) ∈ X ∧ ∀ u ∈ U, (1 : G) * u * (1 : G)⁻¹ * u⁻¹ ∈ V
    exact ⟨X.one_mem, fun u _ => by
      rw [show (1 : G) * u * (1 : G)⁻¹ * u⁻¹ = 1 by group]
      exact V.one_mem⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hxX, hxU⟩ := hx
    obtain ⟨hyX, hyU⟩ := hy
    refine ⟨X.mul_mem hxX hyX, fun u hu => ?_⟩
    have e : x * y * u * (x * y)⁻¹ * u⁻¹ =
        x * (y * u * y⁻¹ * u⁻¹) * x⁻¹ * (x * u * x⁻¹ * u⁻¹) := by
      group
    rw [e]
    exact V.mul_mem (glueB_conj_mem (hXV hxX) (hyU u hu)) (hxU u hu)
  inv_mem' := by
    intro x hx
    obtain ⟨hxX, hxU⟩ := hx
    refine ⟨X.inv_mem hxX, fun u hu => ?_⟩
    have e : x⁻¹ * u * x⁻¹⁻¹ * u⁻¹ = x⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ * x⁻¹⁻¹ := by
      group
    rw [e]
    exact glueB_conj_mem (hXV (X.inv_mem hxX)) (V.inv_mem (hxU u hu))

private theorem glueB_mem_commSub (U : Subgroup G) {V X : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) {x : G} :
    x ∈ glueB_commSub U hXV ↔ x ∈ X ∧ ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ V :=
  Iff.rfl

theorem commutator_le_of_closure {U V X : Subgroup G} {a : G}
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (haX : a ∈ X) (ha : ∀ u ∈ U, a * u * a⁻¹ * u⁻¹ ∈ V)
    (hcl : X ≤ Subgroup.closure {z : G | ∃ x ∈ X, z = x * a * x⁻¹}) : ⁅U, X⁆ ≤ V := by
  have hgen : ∀ x ∈ X, x * a * x⁻¹ ∈ glueB_commSub U hXV := by
    intro x hx
    refine (glueB_mem_commSub U hXV).mpr ⟨X.mul_mem (X.mul_mem hx haX) (X.inv_mem hx),
      fun u hu => ?_⟩
    have hu' : x⁻¹ * u * x⁻¹⁻¹ ∈ U := glueB_conj_mem (hXU (X.inv_mem hx)) hu
    have e : x * a * x⁻¹ * u * (x * a * x⁻¹)⁻¹ * u⁻¹ =
        x * (a * (x⁻¹ * u * x⁻¹⁻¹) * a⁻¹ * (x⁻¹ * u * x⁻¹⁻¹)⁻¹) * x⁻¹ := by
      group
    rw [e]
    exact glueB_conj_mem (hXV hx) (ha _ hu')
  have hsub : {z : G | ∃ x ∈ X, z = x * a * x⁻¹} ⊆ (glueB_commSub U hXV : Set G) := by
    rintro z ⟨x, hx, rfl⟩
    exact hgen x hx
  have hX : X ≤ glueB_commSub U hXV := hcl.trans ((Subgroup.closure_le _).mpr hsub)
  rw [Subgroup.commutator_le]
  intro u hu x hx
  have h : x * u * x⁻¹ * u⁻¹ ∈ V := ((glueB_mem_commSub U hXV).mp (hX hx)).2 u hu
  rw [commutatorElement_def]
  have e : u * x * u⁻¹ * x⁻¹ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by
    group
  rw [e]
  exact V.inv_mem h

end CFSG.RankThree.PartTwo.Sec8.Hering611
