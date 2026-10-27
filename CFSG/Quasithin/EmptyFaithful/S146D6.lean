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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop
import CFSG.Quasithin.EmptyFaithful.S146D6K

public section

set_option maxRecDepth 100000

namespace CFSG.Quasithin.A6Lat

open Equiv Equiv.Perm
open scoped Pointwise

abbrev A := alternatingGroup (Fin 6)

@[expose] def x0 : Perm (Fin 6) := swap 0 2 * swap 1 3

@[expose] def inD0 (g : A) : Prop := (g : Perm (Fin 6)) * x0 = x0 * (g : Perm (Fin 6))

@[expose] def inSa (g : A) : Prop :=
  ((g : Perm (Fin 6)) 4 = 4 ∨ (g : Perm (Fin 6)) 4 = 5) ∧
    ((g : Perm (Fin 6)) 5 = 4 ∨ (g : Perm (Fin 6)) 5 = 5)

@[expose] def mpair (a b : Fin 6) : Prop :=
  (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) ∨ (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) ∨ (a = 4 ∧ b = 5) ∨
    (a = 5 ∧ b = 4)

@[expose] def inSb (g : A) : Prop :=
  mpair ((g : Perm (Fin 6)) 0) ((g : Perm (Fin 6)) 2) ∧
    mpair ((g : Perm (Fin 6)) 1) ((g : Perm (Fin 6)) 3) ∧
    mpair ((g : Perm (Fin 6)) 4) ((g : Perm (Fin 6)) 5)

instance : DecidablePred inD0 := fun g => by unfold inD0; infer_instance
instance : DecidablePred inSa := fun g => by unfold inSa; infer_instance
instance : DecidablePred inSb := fun g => by unfold inSb mpair; infer_instance

@[expose] def mkA (σ : Perm (Fin 6))
    (h : σ ∈ alternatingGroup (Fin 6) := by rw [mem_alternatingGroup]; decide +kernel) : A := ⟨σ, h⟩

@[expose] def c4 : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3

@[expose] def D0list : List A :=
  [1, mkA (swap 0 2 * swap 1 3), mkA (swap 0 1 * swap 2 3), mkA (swap 0 3 * swap 1 2),
   mkA (swap 0 2 * swap 4 5), mkA (swap 1 3 * swap 4 5), mkA (c4 * swap 4 5), mkA (c4⁻¹ * swap 4 5)]

@[expose] def lsA1 : List A := [mkA (swap 0 2 * swap 1 3), mkA (swap 0 1 * swap 2 3)]

@[expose] def lsA2 : List A := [mkA (swap 0 1 * swap 2 3), mkA (swap 0 3 * swap 1 2)]

@[expose] def lsB1 : List A := [mkA (swap 0 2 * swap 1 3), mkA (swap 0 2 * swap 4 5)]

@[expose] def lsB2 : List A := [mkA (swap 0 2 * swap 4 5), mkA (swap 1 3 * swap 4 5)]

@[expose] def c0 : A := mkA (swap 0 1 * swap 1 2)

@[expose] def c1 : A := mkA (swap 0 1 * swap 1 4 * swap 2 3 * swap 3 5)

theorem D0list_sound : ∀ d ∈ D0list, inD0 d := fun _ hd =>
  S146D6K.sound_of S146D6K.pin_D0 S146D6K.check_D0pc (S146D6K.val_mem rfl hd)
theorem lsA1_sound : ∀ d ∈ lsA1, inD0 d := fun _ hd =>
  S146D6K.sound_of S146D6K.pin_A1 S146D6K.check_A1pc (S146D6K.val_mem rfl hd)
theorem lsA2_sound : ∀ d ∈ lsA2, inD0 d := fun _ hd =>
  S146D6K.sound_of S146D6K.pin_A2 S146D6K.check_A2pc (S146D6K.val_mem rfl hd)
theorem lsB1_sound : ∀ d ∈ lsB1, inD0 d := fun _ hd =>
  S146D6K.sound_of S146D6K.pin_B1 S146D6K.check_B1pc (S146D6K.val_mem rfl hd)
theorem lsB2_sound : ∀ d ∈ lsB2, inD0 d := fun _ hd =>
  S146D6K.sound_of S146D6K.pin_B2 S146D6K.check_B2pc (S146D6K.val_mem rfl hd)

theorem inD0_mul : ∀ g : A, inD0 g → ∀ h : A, inD0 h → inD0 (g * h) :=
  fun _ hg _ hh => S146D6K.inD0_mulK hg hh
theorem inD0_inv : ∀ g : A, inD0 g → inD0 g⁻¹ := fun _ hg => S146D6K.inD0_invK hg
theorem inSa_mul : ∀ g : A, inSa g → ∀ h : A, inSa h → inSa (g * h) :=
  fun _ hg _ hh => S146D6K.inSa_mulK hg hh
theorem inSa_inv : ∀ g : A, inSa g → inSa g⁻¹ :=
  fun g hg => S146D6K.inSa_invK (mem_alternatingGroup.1 g.2) hg
theorem inSb_mul : ∀ g : A, inSb g → ∀ h : A, inSb h → inSb (g * h) :=
  fun _ hg _ hh => S146D6K.inSb_mulK hg hh
theorem inSb_inv : ∀ g : A, inSb g → inSb g⁻¹ :=
  fun g hg => S146D6K.inSb_invK (mem_alternatingGroup.1 g.2) hg

theorem inD0_one : inD0 (1 : A) := by decide +kernel
theorem inSa_one : inSa (1 : A) := by decide +kernel
theorem inSb_one : inSb (1 : A) := by decide +kernel

theorem card_D0fin : Fintype.card {g : A // inD0 g} = 8 :=
  (Fintype.card_congr' rfl).trans S146D6K.card_D0K

theorem inD0_inSa : ∀ g : A, inD0 g → inSa g :=
  fun g hg => S146D6K.inD0_inSaK (mem_alternatingGroup.1 g.2) hg
theorem inD0_inSb : ∀ g : A, inD0 g → inSb g :=
  fun g hg => S146D6K.inD0_inSbK (mem_alternatingGroup.1 g.2) hg

theorem dc_a : ∀ g : A, inSa g → ¬ inD0 g → ∀ h : A, inSa h →
    inD0 h ∨ ∃ d ∈ D0list, inD0 (g⁻¹ * (d⁻¹ * h)) := by
  intro g hg hgD h hh
  rcases S146D6K.dcAK (mem_alternatingGroup.1 g.2) hg hgD (mem_alternatingGroup.1 h.2) hh with
    h1 | ⟨δ, hδ, h1⟩
  · exact Or.inl h1
  · obtain ⟨d, hd, rfl⟩ := S146D6K.mem_val (L := D0list) rfl hδ
    exact Or.inr ⟨d, hd, h1⟩

theorem dc_b : ∀ g : A, inSb g → ¬ inD0 g → ∀ h : A, inSb h →
    inD0 h ∨ ∃ d ∈ D0list, inD0 (g⁻¹ * (d⁻¹ * h)) := by
  intro g hg hgD h hh
  rcases S146D6K.dcBK (mem_alternatingGroup.1 g.2) hg hgD (mem_alternatingGroup.1 h.2) hh with
    h1 | ⟨δ, hδ, h1⟩
  · exact Or.inl h1
  · obtain ⟨d, hd, rfl⟩ := S146D6K.mem_val (L := D0list) rfl hδ
    exact Or.inr ⟨d, hd, h1⟩

theorem word6 : ∀ g : A, ¬ inSa g → ¬ inSb g →
    (∃ d ∈ lsA1, ∃ d' ∈ lsA2, inSa (g * d * g⁻¹ * d' * g) ∧ ¬ inD0 (g * d * g⁻¹ * d' * g)) ∧
    (∃ d ∈ lsB1, ∃ d' ∈ lsB2, inSb (g * d * g⁻¹ * d' * g) ∧ ¬ inD0 (g * d * g⁻¹ * d' * g)) := by
  intro g hga hgb
  obtain ⟨⟨δ, hδ, δ', hδ', ha⟩, ⟨ε, hε, ε', hε', hb⟩⟩ :=
    S146D6K.word6K (mem_alternatingGroup.1 g.2) hga hgb
  obtain ⟨d, hd, rfl⟩ := S146D6K.mem_val (L := lsA1) rfl hδ
  obtain ⟨d', hd', rfl⟩ := S146D6K.mem_val (L := lsA2) rfl hδ'
  obtain ⟨e, he, rfl⟩ := S146D6K.mem_val (L := lsB1) rfl hε
  obtain ⟨e', he', rfl⟩ := S146D6K.mem_val (L := lsB2) rfl hε'
  exact ⟨⟨d, hd, d', hd', ha⟩, ⟨e, he, e', he', hb⟩⟩

theorem exists_inSb_not_inSa : ∃ y : A, inSb y ∧ ¬ inSa y :=
  ⟨c1, by decide +kernel, by decide +kernel⟩

theorem cls3 : ∀ x : A, x * x * x = 1 → x ≠ 1 →
    (∃ k : A, k * c0 * k⁻¹ = x) ∨ (∃ k : A, k * c1 * k⁻¹ = x) := by
  intro x h3 h1
  obtain ⟨κ, hκ, h | h⟩ := S146D6K.cls3K (mem_alternatingGroup.1 x.2) (congrArg Subtype.val h3)
    (fun h => h1 (Subtype.ext h))
  · exact Or.inl ⟨⟨κ, mem_alternatingGroup.2 hκ⟩, Subtype.ext h.1⟩
  · exact Or.inr ⟨⟨κ, mem_alternatingGroup.2 hκ⟩, Subtype.ext h.1⟩

theorem Sa_cls : ∀ x : A, inSa x → x * x * x = 1 → x ≠ 1 → ∃ k : A, k * c0 * k⁻¹ = x := by
  intro x hx h3 h1
  obtain ⟨κ, hκ, h | h⟩ := S146D6K.cls3K (mem_alternatingGroup.1 x.2) (congrArg Subtype.val h3)
    (fun h => h1 (Subtype.ext h))
  · exact ⟨⟨κ, mem_alternatingGroup.2 hκ⟩, Subtype.ext h.1⟩
  · exact absurd hx h.2

theorem Sb_cls : ∀ x : A, inSb x → x * x * x = 1 → x ≠ 1 → ∃ k : A, k * c1 * k⁻¹ = x := by
  intro x hx h3 h1
  obtain ⟨κ, hκ, h | h⟩ := S146D6K.cls3K (mem_alternatingGroup.1 x.2) (congrArg Subtype.val h3)
    (fun h => h1 (Subtype.ext h))
  · exact absurd hx h.2
  · exact ⟨⟨κ, mem_alternatingGroup.2 hκ⟩, Subtype.ext h.1⟩

theorem c0_ne_c1 : ¬ ∃ k : A, k * c0 * k⁻¹ = c1 := by
  rintro ⟨k, hk⟩
  exact S146D6K.c0_ne_c1K (mem_alternatingGroup.1 k.2) (congrArg Subtype.val hk)

theorem inSa_c0 : inSa c0 := by decide +kernel
theorem inSb_c1 : inSb c1 := by decide +kernel
theorem c0_cube : c0 * c0 * c0 = 1 := by decide +kernel
theorem c1_cube : c1 * c1 * c1 = 1 := by decide +kernel
theorem c0_ne_one : c0 ≠ 1 := by decide +kernel
theorem c1_ne_one : c1 ≠ 1 := by decide +kernel

theorem inSa_iff : ∀ g : A, inSa g ↔ ∀ y : Fin 6, (y = (g : Perm (Fin 6)) 4 ∨ y = (g : Perm (Fin 6)) 5) ↔
    (y = 4 ∨ y = 5) :=
  fun g => S146D6K.pair45 _ _ ((g : Perm (Fin 6)).injective.ne (by decide))

@[expose] def D0 : Subgroup A where
  carrier := {g | inD0 g}
  one_mem' := inD0_one
  mul_mem' := fun {a b} ha hb => inD0_mul a ha b hb
  inv_mem' := fun {a} ha => inD0_inv a ha

@[expose] def Sa : Subgroup A where
  carrier := {g | inSa g}
  one_mem' := inSa_one
  mul_mem' := fun {a b} ha hb => inSa_mul a ha b hb
  inv_mem' := fun {a} ha => inSa_inv a ha

@[expose] def Sb : Subgroup A where
  carrier := {g | inSb g}
  one_mem' := inSb_one
  mul_mem' := fun {a b} ha hb => inSb_mul a ha b hb
  inv_mem' := fun {a} ha => inSb_inv a ha

theorem mem_D0 {g : A} : g ∈ D0 ↔ inD0 g := Iff.rfl
theorem mem_Sa {g : A} : g ∈ Sa ↔ inSa g := Iff.rfl
theorem mem_Sb {g : A} : g ∈ Sb ↔ inSb g := Iff.rfl

theorem card_D0 : Nat.card D0 = 8 := by
  have h : Nat.card D0 = Nat.card {g : A // inD0 g} := rfl
  rw [h, Nat.card_eq_fintype_card]
  exact card_D0fin

theorem D0_le_Sa : D0 ≤ Sa := fun g hg => inD0_inSa g hg
theorem D0_le_Sb : D0 ≤ Sb := fun g hg => inD0_inSb g hg

theorem Sa_eq_stabilizer : Sa = MulAction.stabilizer A ({4, 5} : Set (Fin 6)) := by
  ext g
  rw [MulAction.mem_stabilizer_iff, mem_Sa, inSa_iff]
  have h1 : g • ({4, 5} : Set (Fin 6)) = {(g : Perm (Fin 6)) 4, (g : Perm (Fin 6)) 5} := by
    rw [Set.smul_set_insert, Set.smul_set_singleton]
    rfl
  rw [h1, Set.ext_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem Sa_isCoatom : IsCoatom Sa := by
  rw [Sa_eq_stabilizer]
  refine alternatingGroup.isCoatom_stabilizer_of_ncard_lt_ncard_compl (α := Fin 6) ?_ ?_
  · exact ⟨4, by simp, 5, by simp, by decide⟩
  · have h1 : ({4, 5} : Set (Fin 6)).ncard = 2 := Set.ncard_pair (by decide)
    have h2 := Set.ncard_add_ncard_compl ({4, 5} : Set (Fin 6))
    rw [h1] at h2 ⊢
    have h3 : Nat.card (Fin 6) = 6 := by simp
    omega

theorem Sa_le_of_mem {P : Subgroup A} (hD : D0 ≤ P) {g : A} (hg : g ∈ Sa) (hgD : g ∉ D0)
    (hgP : g ∈ P) : Sa ≤ P := by
  intro h hh
  rcases dc_a g hg hgD h hh with h1 | ⟨d, hd, hd'⟩
  · exact hD h1
  · have hdD : d ∈ D0 := D0list_sound d hd
    have : h = d * (g * (g⁻¹ * (d⁻¹ * h))) := by group
    rw [this]
    exact P.mul_mem (hD hdD) (P.mul_mem hgP (hD hd'))

theorem Sb_le_of_mem {P : Subgroup A} (hD : D0 ≤ P) {g : A} (hg : g ∈ Sb) (hgD : g ∉ D0)
    (hgP : g ∈ P) : Sb ≤ P := by
  intro h hh
  rcases dc_b g hg hgD h hh with h1 | ⟨d, hd, hd'⟩
  · exact hD h1
  · have hdD : d ∈ D0 := D0list_sound d hd
    have : h = d * (g * (g⁻¹ * (d⁻¹ * h))) := by group
    rw [this]
    exact P.mul_mem (hD hdD) (P.mul_mem hgP (hD hd'))

theorem exists_not_mem_union {P : Subgroup A} (ha : ¬ P ≤ Sa) (hb : ¬ P ≤ Sb) :
    ∃ g ∈ P, g ∉ Sa ∧ g ∉ Sb := by
  by_contra hcon
  push Not at hcon
  obtain ⟨p, hpP, hpa⟩ : ∃ p ∈ P, p ∉ Sa := by
    by_contra h'
    push Not at h'
    exact ha fun x hx => h' x hx
  obtain ⟨q, hqP, hqb⟩ : ∃ q ∈ P, q ∉ Sb := by
    by_contra h'
    push Not at h'
    exact hb fun x hx => h' x hx
  have hpb : p ∈ Sb := hcon p hpP hpa
  have hqa : q ∈ Sa := by
    by_contra h'
    exact hqb (hcon q hqP h')
  by_cases hpq : p * q ∈ Sa
  · apply hpa
    have : p = (p * q) * q⁻¹ := by group
    rw [this]
    exact Sa.mul_mem hpq (Sa.inv_mem hqa)
  · apply hqb
    have hpqb : p * q ∈ Sb := hcon _ (P.mul_mem hpP hqP) hpq
    have : q = p⁻¹ * (p * q) := by group
    rw [this]
    exact Sb.mul_mem (Sb.inv_mem hpb) hpqb

theorem fuse_contra {X : Type*} [Group X] (α : MulAut X) (c₀ c₁ : X)
    (hall : ∀ x : X, x * x * x = 1 → x ≠ 1 →
      (∃ k, k * c₀ * k⁻¹ = x) ∨ (∃ k, k * c₁ * k⁻¹ = x))
    (hne : ¬ ∃ k, k * c₀ * k⁻¹ = c₁) (hα : ∃ n, n * c₀ * n⁻¹ = α c₀)
    (hfuse : ∃ x : X, x * x * x = 1 ∧ x ≠ 1 ∧ ∀ k : X, k * x * k⁻¹ ≠ α x) : False := by
  obtain ⟨x, hx3, hx1, hx⟩ := hfuse
  obtain ⟨n, hn⟩ := hα
  have hαx3 : α x * α x * α x = 1 := by
    rw [← map_mul, ← map_mul, hx3, map_one]
  have hαx1 : α x ≠ 1 := fun h => hx1 (α.injective (by rw [h, map_one]))
  rcases hall x hx3 hx1 with ⟨k, hk⟩ | ⟨k, hk⟩
  · apply hx (α k * n * k⁻¹)
    rw [← hk, map_mul, map_mul, map_inv, ← hn]
    group
  · rcases hall (α x) hαx3 hαx1 with ⟨m, hm⟩ | ⟨m, hm⟩
    · apply hne
      refine ⟨k⁻¹ * α.symm (m * n⁻¹), ?_⟩
      have h1 : α (α.symm (m * n⁻¹) * c₀ * (α.symm (m * n⁻¹))⁻¹) = α x := by
        rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hm, ← hn]
        group
      have h2 := α.injective h1
      calc k⁻¹ * α.symm (m * n⁻¹) * c₀ * (k⁻¹ * α.symm (m * n⁻¹))⁻¹
          = k⁻¹ * (α.symm (m * n⁻¹) * c₀ * (α.symm (m * n⁻¹))⁻¹) * k := by group
        _ = k⁻¹ * x * k := by rw [h2]
        _ = c₁ := by rw [← hk]; group
    · apply hx (m * k⁻¹)
      rw [← hm, ← hk]
      group

theorem order_three_alpha (α : MulAut A) {x : A} (h3 : x * x * x = 1) (h1 : x ≠ 1) :
    α x * α x * α x = 1 ∧ α x ≠ 1 :=
  ⟨by rw [← map_mul, ← map_mul, h3, map_one], fun h => h1 (α.injective (by rw [h, map_one]))⟩

theorem eq_D0_or_top {P : Subgroup A} (hD : D0 ≤ P) (α : MulAut A) (hα : ∀ x ∈ P, α x ∈ P)
    (hfuse : ∃ x : A, x * x * x = 1 ∧ x ≠ 1 ∧ ∀ k : A, k * x * k⁻¹ ≠ α x) : P = D0 ∨ P = ⊤ := by
  have hc1c0 : ¬ ∃ k : A, k * c1 * k⁻¹ = c0 := by
    rintro ⟨k, hk⟩
    exact c0_ne_c1 ⟨k⁻¹, by rw [← hk]; group⟩
  by_cases hPa : P ≤ Sa
  · left
    by_contra hne
    obtain ⟨g, hgP, hgD⟩ : ∃ g ∈ P, g ∉ D0 := by
      by_contra h'
      push Not at h'
      exact hne (le_antisymm (fun x hx => h' x hx) hD)
    have hSaP : Sa ≤ P := Sa_le_of_mem hD (hPa hgP) hgD hgP
    have hSa : ∀ x ∈ Sa, α x ∈ Sa := fun x hx => hPa (hα x (hSaP hx))
    obtain ⟨h3, h1⟩ := order_three_alpha α c0_cube c0_ne_one
    exact fuse_contra α c0 c1 cls3 c0_ne_c1 (Sa_cls _ (hSa c0 inSa_c0) h3 h1) hfuse
  by_cases hPb : P ≤ Sb
  · left
    by_contra hne
    obtain ⟨g, hgP, hgD⟩ : ∃ g ∈ P, g ∉ D0 := by
      by_contra h'
      push Not at h'
      exact hne (le_antisymm (fun x hx => h' x hx) hD)
    have hSbP : Sb ≤ P := Sb_le_of_mem hD (hPb hgP) hgD hgP
    have hSb : ∀ x ∈ Sb, α x ∈ Sb := fun x hx => hPb (hα x (hSbP hx))
    obtain ⟨h3, h1⟩ := order_three_alpha α c1_cube c1_ne_one
    exact fuse_contra α c1 c0 (fun x a b => (cls3 x a b).symm) hc1c0
      (Sb_cls _ (hSb c1 inSb_c1) h3 h1) hfuse
  right
  obtain ⟨g, hgP, hga, hgb⟩ := exists_not_mem_union hPa hPb
  obtain ⟨⟨d, hd, d', hd', hwa, hwa'⟩, ⟨e, he, e', he', hwb, hwb'⟩⟩ := word6 g hga hgb
  have hmem : ∀ d d' : A, d ∈ D0 → d' ∈ D0 → g * d * g⁻¹ * d' * g ∈ P := fun d d' hd hd' =>
    P.mul_mem (P.mul_mem (P.mul_mem (P.mul_mem hgP (hD hd)) (P.inv_mem hgP)) (hD hd')) hgP
  have hSaP : Sa ≤ P :=
    Sa_le_of_mem hD (g := g * d * g⁻¹ * d' * g) hwa hwa' (hmem d d' (lsA1_sound d hd)
      (lsA2_sound d' hd'))
  have hSbP : Sb ≤ P :=
    Sb_le_of_mem hD (g := g * e * g⁻¹ * e' * g) hwb hwb' (hmem e e' (lsB1_sound e he)
      (lsB2_sound e' he'))
  obtain ⟨y, hyb, hya⟩ := exists_inSb_not_inSa
  rcases Sa_isCoatom.le_iff.mp hSaP with h | h
  · exact h
  · have hyP : y ∈ P := hSbP hyb
    rw [h] at hyP
    exact absurd hyP hya

theorem card_A : Nat.card A = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem exists_sylow_eq {D : Subgroup A} (hD : Nat.card D = 8) : ∃ S : Sylow 2 A, (S : Subgroup A) = D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDp : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [hD]; norm_num)
  obtain ⟨S, hS⟩ := hDp.exists_le_sylow
  refine ⟨S, ?_⟩
  have hSp : IsPGroup 2 (S : Subgroup A) := S.isPGroup'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hSp
  have hdvd : Nat.card (S : Subgroup A) ∣ 360 := card_A ▸ Subgroup.card_subgroup_dvd_card _
  have hle : Nat.card D ∣ Nat.card (S : Subgroup A) := Subgroup.card_dvd_of_le hS
  have h8 : Nat.card (S : Subgroup A) = 8 := by
    rw [hD, hk] at hle
    rw [hk] at hdvd
    have hk3 : k = 3 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · interval_cases k <;> simp at hle
      · have h16 : 2 ^ 4 ∣ 2 ^ k := Nat.pow_dvd_pow 2 h
        have := h16.trans hdvd
        norm_num at this
    rw [hk, hk3]; norm_num
  exact (Subgroup.eq_of_le_of_card_ge hS (by rw [h8, hD])).symm

theorem exists_conj_D0 (D : Subgroup A) (hD : Nat.card D = 8) :
    ∃ g : A, ∀ x : A, x ∈ D ↔ g⁻¹ * x * g ∈ D0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_sylow_eq hD
  obtain ⟨S₀, hS₀⟩ := exists_sylow_eq card_D0
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A S₀ S
  refine ⟨g, fun x => ?_⟩
  have h1 : ((g • S₀ : Sylow 2 A) : Subgroup A) = D := by rw [hg, hS]
  rw [Sylow.coe_subgroup_smul, hS₀] at h1
  rw [← h1, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hs
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem eq_or_top_of_fuse_A (D P : Subgroup A) (hD : Nat.card D = 8) (hDP : D ≤ P) (α : MulAut A)
    (hαP : ∀ x ∈ P, α x ∈ P)
    (hfuse : ∃ x : A, x * x * x = 1 ∧ x ≠ 1 ∧ ∀ k : A, k * x * k⁻¹ ≠ α x) : P = D ∨ P = ⊤ := by
  obtain ⟨g, hg⟩ := exists_conj_D0 D hD
  let P' : Subgroup A := P.comap (MulAut.conj g).toMonoidHom
  have hP'mem : ∀ y : A, y ∈ P' ↔ g * y * g⁻¹ ∈ P := fun y => by simp [P', MulAut.conj_apply]
  let α' : MulAut A := ((MulAut.conj g).trans α).trans (MulAut.conj g⁻¹)
  have hα' : ∀ y : A, α' y = g⁻¹ * α (g * y * g⁻¹) * g := fun y => by
    simp [α', MulAut.conj_apply]
  have hD0P' : D0 ≤ P' := by
    intro y hy
    rw [hP'mem]
    apply hDP
    rw [hg]
    simpa [mul_assoc] using hy
  have hαP' : ∀ x ∈ P', α' x ∈ P' := by
    intro x hx
    rw [hα', hP'mem]
    have h1 := hαP _ ((hP'mem x).mp hx)
    simpa [mul_assoc] using h1
  have hfuse' : ∃ x : A, x * x * x = 1 ∧ x ≠ 1 ∧ ∀ k : A, k * x * k⁻¹ ≠ α' x := by
    obtain ⟨x, hx3, hx1, hx⟩ := hfuse
    refine ⟨g⁻¹ * x * g, ?_, ?_, fun k hk => ?_⟩
    · have : g⁻¹ * x * g * (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x * x) * g := by group
      rw [this, hx3]
      group
    · intro h
      apply hx1
      have : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      rw [this, h]
      group
    · apply hx (g * k * g⁻¹)
      rw [hα'] at hk
      have h2 : g * (k * (g⁻¹ * x * g) * k⁻¹) * g⁻¹ = g * (g⁻¹ * α (g * (g⁻¹ * x * g) * g⁻¹) * g) * g⁻¹ := by
        rw [hk]
      have e1 : g * (g⁻¹ * α (g * (g⁻¹ * x * g) * g⁻¹) * g) * g⁻¹ = α x := by
        have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
        rw [this]
        group
      rw [e1] at h2
      rw [← h2]
      group
  rcases eq_D0_or_top hD0P' α' hαP' hfuse' with h | h
  · left
    apply le_antisymm
    · intro x hx
      have : g⁻¹ * x * g ∈ P' := by
        rw [hP'mem]; simpa [mul_assoc] using hx
      rw [h] at this
      rw [hg]; exact this
    · exact hDP
  · right
    rw [eq_top_iff]
    intro x _
    have : g⁻¹ * x * g ∈ P' := by rw [h]; exact Subgroup.mem_top _
    rw [hP'mem] at this
    simpa [mul_assoc] using this

theorem eq_or_top_of_fuse {X : Type*} [Group X] (e : X ≃* A) (D P : Subgroup X) (hD : Nat.card D = 8)
    (hDP : D ≤ P) (α : MulAut X) (hαP : ∀ x ∈ P, α x ∈ P)
    (hfuse : ∃ x : X, x * x * x = 1 ∧ x ≠ 1 ∧ ∀ k : X, k * x * k⁻¹ ≠ α x) : P = D ∨ P = ⊤ := by
  let D' : Subgroup A := D.map e.toMonoidHom
  let P' : Subgroup A := P.map e.toMonoidHom
  let α' : MulAut A := (e.symm.trans α).trans e
  have hα' : ∀ a : A, α' a = e (α (e.symm a)) := fun a => rfl
  have hD' : Nat.card D' = 8 := by
    rw [← hD]
    exact Nat.card_congr (D.equivMapOfInjective e.toMonoidHom e.injective).symm.toEquiv
  have hDP' : D' ≤ P' := Subgroup.map_mono hDP
  have hαP' : ∀ x ∈ P', α' x ∈ P' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [hα']
    exact Subgroup.mem_map.mpr ⟨α y, hαP y hy, by simp⟩
  have hfuse' : ∃ x : A, x * x * x = 1 ∧ x ≠ 1 ∧ ∀ k : A, k * x * k⁻¹ ≠ α' x := by
    obtain ⟨x, hx3, hx1, hx⟩ := hfuse
    refine ⟨e x, ?_, ?_, fun k hk => ?_⟩
    · rw [← map_mul, ← map_mul, hx3, map_one]
    · intro h
      exact hx1 (e.injective (by rw [h, map_one]))
    · apply hx (e.symm k)
      apply e.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      rw [hα'] at hk
      simpa using hk
  rcases eq_or_top_of_fuse_A D' P' hD' hDP' α' hαP' hfuse' with h | h
  · left
    exact Subgroup.map_injective e.injective h
  · right
    have : P.map e.toMonoidHom = (⊤ : Subgroup X).map e.toMonoidHom := by
      rw [Subgroup.map_top_of_surjective _ e.surjective]
      exact h
    exact Subgroup.map_injective e.injective this

end CFSG.Quasithin.A6Lat
