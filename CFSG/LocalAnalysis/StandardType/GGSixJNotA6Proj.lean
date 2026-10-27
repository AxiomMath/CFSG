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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

namespace CFSG.StandardType

section Proj

variable {G : Type*} [Group G]

@[expose] def ggProjLeft (L C T : Subgroup G) (hLC : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) :
    Subgroup G where
  carrier := {l | l ∈ L ∧ ∃ c ∈ C, l * c ∈ T}
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨haL, c₁, hc₁C, hac₁T⟩ := ha
    obtain ⟨hbL, c₂, hc₂C, hbc₂T⟩ := hb
    refine ⟨L.mul_mem haL hbL, c₁ * c₂, C.mul_mem hc₁C hc₂C, ?_⟩
    have h : (a * b) * (c₁ * c₂) = (a * c₁) * (b * c₂) := by
      calc (a * b) * (c₁ * c₂) = a * (b * c₁) * c₂ := by group
        _ = a * (c₁ * b) * c₂ := by rw [hLC b hbL c₁ hc₁C]
        _ = (a * c₁) * (b * c₂) := by group
    rw [h]
    exact T.mul_mem hac₁T hbc₂T
  one_mem' := ⟨L.one_mem, 1, C.one_mem, by simpa using T.one_mem⟩
  inv_mem' := fun {a} ha => by
    obtain ⟨haL, c, hcC, hacT⟩ := ha
    refine ⟨L.inv_mem haL, c⁻¹, C.inv_mem hcC, ?_⟩
    have h : a⁻¹ * c⁻¹ = (a * c)⁻¹ := by
      rw [hLC a haL c hcC]
      group
    rw [h]
    exact T.inv_mem hacT

@[expose] def ggProjRight (L C T : Subgroup G) (hLC : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) :
    Subgroup G where
  carrier := {c | c ∈ C ∧ ∃ l ∈ L, l * c ∈ T}
  mul_mem' := fun {a b} ha hb => by
    obtain ⟨haC, l₁, hl₁L, hl₁aT⟩ := ha
    obtain ⟨hbC, l₂, hl₂L, hl₂bT⟩ := hb
    refine ⟨C.mul_mem haC hbC, l₁ * l₂, L.mul_mem hl₁L hl₂L, ?_⟩
    have h : (l₁ * l₂) * (a * b) = (l₁ * a) * (l₂ * b) := by
      calc (l₁ * l₂) * (a * b) = l₁ * (l₂ * a) * b := by group
        _ = l₁ * (a * l₂) * b := by rw [hLC l₂ hl₂L a haC]
        _ = (l₁ * a) * (l₂ * b) := by group
    rw [h]
    exact T.mul_mem hl₁aT hl₂bT
  one_mem' := ⟨C.one_mem, 1, L.one_mem, by simpa using T.one_mem⟩
  inv_mem' := fun {a} ha => by
    obtain ⟨haC, l, hlL, hlaT⟩ := ha
    refine ⟨C.inv_mem haC, l⁻¹, L.inv_mem hlL, ?_⟩
    have h : l⁻¹ * a⁻¹ = (l * a)⁻¹ := by
      rw [hLC l hlL a haC]
      group
    rw [h]
    exact T.inv_mem hlaT

variable {L C T : Subgroup G} {hLC : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l}

theorem mem_ggProjLeft {l : G} :
    l ∈ ggProjLeft L C T hLC ↔ l ∈ L ∧ ∃ c ∈ C, l * c ∈ T := Iff.rfl

theorem mem_ggProjRight {c : G} :
    c ∈ ggProjRight L C T hLC ↔ c ∈ C ∧ ∃ l ∈ L, l * c ∈ T := Iff.rfl

theorem ggProjLeft_le_left : ggProjLeft L C T hLC ≤ L := fun _ hx => hx.1

theorem pow_eq_one_of_mul_pow_eq_one
    (hCL : ∀ c ∈ C, ∀ y ∈ L, c * y = y * c)
    (htriv : ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z = 1)
    {l c : G} (hl : l ∈ L) (hc : c ∈ C) (hlc : l * c = c * l) {m : ℕ} (h : (l * c) ^ m = 1) :
    l ^ m = 1 ∧ c ^ m = 1 := by
  have hcomm : Commute l c := hlc
  have hpow : l ^ m * c ^ m = 1 := by
    rw [← hcomm.mul_pow m]
    exact h
  have hlm : l ^ m ∈ L := L.pow_mem hl m
  have hcm : c ^ m ∈ C := C.pow_mem hc m
  have hlm_eq : l ^ m = (c ^ m)⁻¹ := eq_inv_iff_mul_eq_one.mpr hpow
  have hcomm_lm : ∀ y ∈ L, l ^ m * y = y * l ^ m := by
    intro y hy
    rw [hlm_eq]
    exact (Commute.inv_left (hCL (c ^ m) hcm y hy))
  have hlm_one : l ^ m = 1 := htriv (l ^ m) hlm hcomm_lm
  refine ⟨hlm_one, ?_⟩
  rw [hlm_one, one_mul] at hpow
  exact hpow

theorem isPGroup_ggProjLeft (htriv : ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z = 1) {q : ℕ}
    (hT : IsPGroup q T) : IsPGroup q (ggProjLeft L C T hLC) := by
  intro g
  obtain ⟨hlL, c, hcC, hlcT⟩ := (mem_ggProjLeft).mp g.2
  obtain ⟨n, hn⟩ := hT ⟨(g : G) * c, hlcT⟩
  have hn' : ((g : G) * c) ^ (q ^ n) = 1 := by
    have := congrArg (fun x : ↥T => (x : G)) hn
    simpa using this
  have hcomm : (g : G) * c = c * (g : G) := hLC (g : G) hlL c hcC
  obtain ⟨hlm, -⟩ := pow_eq_one_of_mul_pow_eq_one
    (fun c' hc' y hy => (hLC y hy c' hc').symm) htriv hlL hcC hcomm hn'
  refine ⟨n, ?_⟩
  apply Subtype.ext
  simpa using hlm

theorem pow_eq_one_of_mem_ggProjRight (htriv : ∀ z ∈ L, (∀ y ∈ L, z * y = y * z) → z = 1)
    {m : ℕ} (hT : ∀ g ∈ T, g ^ m = 1) : ∀ c ∈ ggProjRight L C T hLC, c ^ m = 1 := by
  intro c hc
  obtain ⟨hcC, l, hlL, hlcT⟩ := (mem_ggProjRight).mp hc
  have hcomm : l * c = c * l := hLC l hlL c hcC
  have h : (l * c) ^ m = 1 := hT (l * c) hlcT
  exact (pow_eq_one_of_mul_pow_eq_one
    (fun c' hc' y hy => (hLC y hy c' hc').symm) htriv hlL hcC hcomm h).2

theorem conj_mem_ggProjLeft {b : G} (hbL : ∀ l ∈ L, b * l * b⁻¹ ∈ L)
    (hbC : ∀ c ∈ C, b * c * b⁻¹ ∈ C) (hbT : ∀ t ∈ T, b * t * b⁻¹ ∈ T) {l : G}
    (hl : l ∈ ggProjLeft L C T hLC) : b * l * b⁻¹ ∈ ggProjLeft L C T hLC := by
  obtain ⟨hlL, c, hcC, hlcT⟩ := (mem_ggProjLeft).mp hl
  refine (mem_ggProjLeft).mpr ⟨hbL l hlL, b * c * b⁻¹, hbC c hcC, ?_⟩
  have h : (b * l * b⁻¹) * (b * c * b⁻¹) = b * (l * c) * b⁻¹ := by group
  rw [h]
  exact hbT (l * c) hlcT

theorem le_right_of_ggProjLeft_eq_bot (hdec : ∀ g ∈ T, ∃ l ∈ L, ∃ c ∈ C, g = l * c)
    (hbot : ggProjLeft L C T hLC = ⊥) : T ≤ C := by
  intro g hgT
  obtain ⟨l, hlL, c, hcC, rfl⟩ := hdec g hgT
  have hl_mem : l ∈ ggProjLeft L C T hLC :=
    (mem_ggProjLeft).mpr ⟨hlL, c, hcC, hgT⟩
  rw [hbot] at hl_mem
  have hl_one : l = 1 := by simpa using hl_mem
  rw [hl_one, one_mul]
  exact hcC

end Proj

end CFSG.StandardType
