module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin.HSType

@[expose] def aA5 : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def bA5 : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 2 4

@[expose] def aA4 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def bA4 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def evalA5 : List Bool → Equiv.Perm (Fin 5)
  | [] => 1
  | b :: w => (if b then bA5 else aA5) * evalA5 w

@[expose] def evalA4 : List Bool → Equiv.Perm (Fin 4)
  | [] => 1
  | b :: w => (if b then bA4 else aA4) * evalA4 w

@[expose] def wordsA5 : List (List Bool) :=
    [[], [false], [true], [true, false], [false, true], [true, true], [false, true, false],
     [true, true, false], [true, false, true], [false, true, true], [true, false, true, false],
     [false, true, true, false], [false, true, false, true], [true, true, false, true],
     [true, false, true, true], [false, true, false, true, false], [true, true, false, true, false],
     [true, false, true, true, false], [true, false, true, false, true],
     [false, true, true, false, true], [false, true, false, true, true],
     [true, true, false, true, true], [true, false, true, false, true, false],
     [false, true, true, false, true, false], [false, true, false, true, true, false],
     [true, true, false, true, true, false], [true, true, false, true, false, true],
     [true, false, true, true, false, true], [true, false, true, false, true, true],
     [true, true, false, true, false, true, false], [true, false, true, true, false, true, false],
     [true, false, true, false, true, true, false], [false, true, true, false, true, false, true],
     [false, true, false, true, true, false, true], [true, true, false, true, true, false, true],
     [true, true, false, true, false, true, true],
     [false, true, true, false, true, false, true, false],
     [false, true, false, true, true, false, true, false],
     [true, true, false, true, true, false, true, false],
     [true, true, false, true, false, true, true, false],
     [true, false, true, true, false, true, false, true],
     [true, false, true, false, true, true, false, true],
     [false, true, true, false, true, false, true, true],
     [true, false, true, true, false, true, false, true, false],
     [true, false, true, false, true, true, false, true, false],
     [false, true, true, false, true, false, true, true, false],
     [false, true, false, true, true, false, true, false, true],
     [true, true, false, true, true, false, true, false, true],
     [true, true, false, true, false, true, true, false, true],
     [true, false, true, true, false, true, false, true, true],
     [false, true, false, true, true, false, true, false, true, false],
     [true, true, false, true, true, false, true, false, true, false],
     [true, true, false, true, false, true, true, false, true, false],
     [true, false, true, true, false, true, false, true, true, false],
     [false, true, true, false, true, false, true, true, false, true],
     [false, true, false, true, true, false, true, false, true, true],
     [false, true, true, false, true, false, true, true, false, true, false],
     [false, true, false, true, true, false, true, false, true, true, false],
     [true, false, true, true, false, true, false, true, true, false, true],
     [true, false, true, true, false, true, false, true, true, false, true, false]]

@[expose] def wordsA4 : List (List Bool) :=
    [[], [false], [true], [true, false], [false, true], [true, true], [false, true, false],
     [true, true, false], [true, false, true], [false, true, true], [true, true, false, true],
     [true, false, true, true]]

theorem exists_wordA5 : ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 →
    ∃ w ∈ wordsA5, evalA5 w = σ := by
  decide +kernel

theorem exists_wordA4 : ∀ σ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ = 1 →
    ∃ w ∈ wordsA4, evalA4 w = σ := by
  decide +kernel

theorem evalA5_mem (w : List Bool) : evalA5 w ∈ Subgroup.closure {aA5, bA5} := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons b w ih =>
    refine Subgroup.mul_mem _ ?_ ih
    cases b
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem evalA4_mem (w : List Bool) : evalA4 w ∈ Subgroup.closure {aA4, bA4} := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons b w ih =>
    refine Subgroup.mul_mem _ ?_ ih
    cases b
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem aA5_mem : aA5 ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem bA5_mem : bA5 ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem aA4_mem : aA4 ∈ alternatingGroup (Fin 4) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem bA4_mem : bA4 ∈ alternatingGroup (Fin 4) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem closure_a5_b5 : Subgroup.closure {aA5, bA5} = alternatingGroup (Fin 5) := by
  refine le_antisymm ?_ fun σ hσ => ?_
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact aA5_mem
    · exact bA5_mem
  · obtain ⟨w, -, rfl⟩ := exists_wordA5 σ (Equiv.Perm.mem_alternatingGroup.mp hσ)
    exact evalA5_mem w

theorem closure_a4_b4 : Subgroup.closure {aA4, bA4} = alternatingGroup (Fin 4) := by
  refine le_antisymm ?_ fun σ hσ => ?_
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact aA4_mem
    · exact bA4_mem
  · obtain ⟨w, -, rfl⟩ := exists_wordA4 σ (Equiv.Perm.mem_alternatingGroup.mp hσ)
    exact evalA4_mem w

theorem exists_conj_genA5 : ∀ x y : Equiv.Perm (Fin 5),
    (x * x = 1 ∧ x ≠ 1 ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ (x * y) ^ 5 = 1 ∧ x * y ≠ 1) →
    ∃ ρ : Equiv.Perm (Fin 5), ρ * aA5 * ρ⁻¹ = x ∧ ρ * bA5 * ρ⁻¹ = y := by
  decide +kernel

theorem exists_conj_genA4 : ∀ x y : Equiv.Perm (Fin 4),
    (Equiv.Perm.sign x = 1 ∧ x * x = 1 ∧ x ≠ 1 ∧ y ^ 3 = 1 ∧ y ≠ 1 ∧ (x * y) ^ 3 = 1 ∧
      x * y ≠ 1) →
    ∃ ρ : Equiv.Perm (Fin 4), ρ * aA4 * ρ⁻¹ = x ∧ ρ * bA4 * ρ⁻¹ = y := by
  decide +kernel

theorem eq_one_of_comm_alt_five : ∀ ρ : Equiv.Perm (Fin 5),
    (ρ * aA5 = aA5 * ρ ∧ ρ * bA5 = bA5 * ρ) → ρ = 1 := by
  decide +kernel

theorem eq_one_of_comm_alt_four : ∀ ρ : Equiv.Perm (Fin 4),
    (ρ * aA4 = aA4 * ρ ∧ ρ * bA4 = bA4 * ρ) → ρ = 1 := by
  decide +kernel

theorem alt_five_aut_conj (α : ↥(alternatingGroup (Fin 5)) ≃* ↥(alternatingGroup (Fin 5))) :
    ∃ ρ : Equiv.Perm (Fin 5), ∀ σ : ↥(alternatingGroup (Fin 5)),
      ((α σ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = ρ * σ * ρ⁻¹ := by
  set a : ↥(alternatingGroup (Fin 5)) := ⟨aA5, aA5_mem⟩ with ha
  set b : ↥(alternatingGroup (Fin 5)) := ⟨bA5, bA5_mem⟩ with hb
  have hne : ∀ g : ↥(alternatingGroup (Fin 5)), (g : Equiv.Perm (Fin 5)) ≠ 1 →
      ((α g : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) ≠ 1 := fun g hg h =>
    hg (congrArg Subtype.val (α.injective ((Subtype.ext h).trans (map_one α).symm)))
  have haa : a * a = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ha]
    decide)
  have hb3 : b ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hb]
    decide)
  have hab : (a * b) ^ 5 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_mul, ha, hb]
    decide)
  have hx2 : ((α a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) * (α a) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, haa, map_one, Subgroup.coe_one]
  have hy3 : ((α b : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hb3, map_one, Subgroup.coe_one]
  have hxy : (((α a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) * (α b)) ^ 5 = 1 := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_pow, ← map_mul, ← map_pow, hab, map_one,
      Subgroup.coe_one]
  have hx1 := hne a (by rw [ha]; decide)
  have hy1 := hne b (by rw [hb]; decide)
  have hxy1 : ((α a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) * (α b) ≠ 1 := by
    rw [← Subgroup.coe_mul, ← map_mul]
    exact hne (a * b) (by rw [Subgroup.coe_mul, ha, hb]; decide)
  obtain ⟨ρ, hρa, hρb⟩ := exists_conj_genA5 _ _ ⟨hx2, hx1, hy3, hy1, hxy, hxy1⟩
  refine ⟨ρ, fun σ => ?_⟩
  set f : ↥(alternatingGroup (Fin 5)) →* Equiv.Perm (Fin 5) :=
    (alternatingGroup (Fin 5)).subtype.comp α.toMonoidHom with hf
  set g : ↥(alternatingGroup (Fin 5)) →* Equiv.Perm (Fin 5) :=
    (MulAut.conj ρ).toMonoidHom.comp (alternatingGroup (Fin 5)).subtype with hg
  have hcl : Subgroup.closure ({a, b} : Set ↥(alternatingGroup (Fin 5))) = ⊤ := by
    apply Subgroup.map_injective (alternatingGroup (Fin 5)).subtype_injective
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact closure_a5_b5
  have hfg : f = g := by
    refine MonoidHom.eq_of_eqOn_dense hcl ?_
    rintro _ (rfl | rfl)
    · show ((α a : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = ρ * aA5 * ρ⁻¹
      rw [hρa]
    · show ((α b : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) = ρ * bA5 * ρ⁻¹
      rw [hρb]
  exact congrArg (fun F : ↥(alternatingGroup (Fin 5)) →* Equiv.Perm (Fin 5) => F σ) hfg

theorem alt_four_aut_conj (α : ↥(alternatingGroup (Fin 4)) ≃* ↥(alternatingGroup (Fin 4))) :
    ∃ ρ : Equiv.Perm (Fin 4), ∀ σ : ↥(alternatingGroup (Fin 4)),
      ((α σ : ↥(alternatingGroup (Fin 4))) : Equiv.Perm (Fin 4)) = ρ * σ * ρ⁻¹ := by
  set a : ↥(alternatingGroup (Fin 4)) := ⟨aA4, aA4_mem⟩ with ha
  set b : ↥(alternatingGroup (Fin 4)) := ⟨bA4, bA4_mem⟩ with hb
  have hne : ∀ g : ↥(alternatingGroup (Fin 4)), (g : Equiv.Perm (Fin 4)) ≠ 1 →
      ((α g : ↥(alternatingGroup (Fin 4))) : Equiv.Perm (Fin 4)) ≠ 1 := fun g hg h =>
    hg (congrArg Subtype.val (α.injective ((Subtype.ext h).trans (map_one α).symm)))
  have haa : a * a = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, ha]
    decide)
  have hb3 : b ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, hb]
    decide)
  have hab : (a * b) ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_mul, ha, hb]
    decide)
  have hx2 : ((α a : ↥(alternatingGroup (Fin 4))) : Equiv.Perm (Fin 4)) * (α a) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, haa, map_one, Subgroup.coe_one]
  have hy3 : ((α b : ↥(alternatingGroup (Fin 4))) : Equiv.Perm (Fin 4)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hb3, map_one, Subgroup.coe_one]
  have hxy : (((α a : ↥(alternatingGroup (Fin 4))) : Equiv.Perm (Fin 4)) * (α b)) ^ 3 = 1 := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_pow, ← map_mul, ← map_pow, hab, map_one,
      Subgroup.coe_one]
  have hx1 := hne a (by rw [ha]; decide)
  have hy1 := hne b (by rw [hb]; decide)
  have hxy1 : ((α a : ↥(alternatingGroup (Fin 4))) : Equiv.Perm (Fin 4)) * (α b) ≠ 1 := by
    rw [← Subgroup.coe_mul, ← map_mul]
    exact hne (a * b) (by rw [Subgroup.coe_mul, ha, hb]; decide)
  obtain ⟨ρ, hρa, hρb⟩ := exists_conj_genA4 _ _
    ⟨Equiv.Perm.mem_alternatingGroup.mp (α a).2, hx2, hx1, hy3, hy1, hxy, hxy1⟩
  refine ⟨ρ, fun σ => ?_⟩
  set f : ↥(alternatingGroup (Fin 4)) →* Equiv.Perm (Fin 4) :=
    (alternatingGroup (Fin 4)).subtype.comp α.toMonoidHom with hf
  set g : ↥(alternatingGroup (Fin 4)) →* Equiv.Perm (Fin 4) :=
    (MulAut.conj ρ).toMonoidHom.comp (alternatingGroup (Fin 4)).subtype with hg
  have hcl : Subgroup.closure ({a, b} : Set ↥(alternatingGroup (Fin 4))) = ⊤ := by
    apply Subgroup.map_injective (alternatingGroup (Fin 4)).subtype_injective
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact closure_a4_b4
  have hfg : f = g := by
    refine MonoidHom.eq_of_eqOn_dense hcl ?_
    rintro _ (rfl | rfl)
    · show ((α a : ↥(alternatingGroup (Fin 4))) : Equiv.Perm (Fin 4)) = ρ * aA4 * ρ⁻¹
      rw [hρa]
    · show ((α b : ↥(alternatingGroup (Fin 4))) : Equiv.Perm (Fin 4)) = ρ * bA4 * ρ⁻¹
      rw [hρb]
  exact congrArg (fun F : ↥(alternatingGroup (Fin 4)) →* Equiv.Perm (Fin 4) => F σ) hfg

end CFSG.Quasithin.HSType
