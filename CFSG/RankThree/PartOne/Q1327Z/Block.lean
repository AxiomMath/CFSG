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

namespace CFSG.RankThree.PartOne.Q1327Z

open scoped commutatorElement

section Simple

variable {Γ : Type*} [Group Γ]

theorem exists_noncomm_of_simple {B : Subgroup Γ}
    (hsimple : ∀ N : Subgroup Γ, N ≤ B → (N.subgroupOf B).Normal → N = ⊥ ∨ N = B)
    (hperf : ⁅B, B⁆ = B) (hne : B ≠ ⊥) {l : Γ} (hl : l ∈ B) (hl1 : l ≠ 1) :
    ∃ y ∈ B, ¬ Commute l (y * l * y⁻¹) := by
  by_contra hcon
  push Not at hcon
  let k : Set Γ := {x | ∃ y ∈ B, x = y * l * y⁻¹}
  have hkB : ∀ x ∈ k, x ∈ B := by
    rintro _ ⟨y, hy, rfl⟩
    exact B.mul_mem (B.mul_mem hy hl) (B.inv_mem hy)
  let N : Subgroup Γ := Subgroup.closure k
  have hNB : N ≤ B := (Subgroup.closure_le B).2 hkB
  have hlN : l ∈ N := Subgroup.subset_closure ⟨1, B.one_mem, by simp⟩
  have hNne : N ≠ ⊥ := fun h => hl1 (by simpa [h] using hlN)
  have hconj : ∀ b ∈ B, ∀ x ∈ k, b * x * b⁻¹ ∈ k := by
    rintro b hb _ ⟨y, hy, rfl⟩
    exact ⟨b * y, B.mul_mem hb hy, by group⟩
  have hNnorm : (N.subgroupOf B).Normal := by
    refine ⟨fun x hx b => ?_⟩
    have hx' : (x : Γ) ∈ N := hx
    have : ∀ z ∈ N, (b : Γ) * z * (b : Γ)⁻¹ ∈ N := by
      intro z hz
      refine Subgroup.closure_induction (p := fun z _ => (b : Γ) * z * (b : Γ)⁻¹ ∈ N) ?_ ?_ ?_ ?_ hz
      · intro x hx
        exact Subgroup.subset_closure (hconj b b.2 x hx)
      · simp
      · intro x y _ _ hx hy
        have : (b : Γ) * (x * y) * (b : Γ)⁻¹ =
            ((b : Γ) * x * (b : Γ)⁻¹) * ((b : Γ) * y * (b : Γ)⁻¹) := by group
        rw [this]
        exact N.mul_mem hx hy
      · intro x _ hx
        have : (b : Γ) * x⁻¹ * (b : Γ)⁻¹ = ((b : Γ) * x * (b : Γ)⁻¹)⁻¹ := by group
        rw [this]
        exact N.inv_mem hx
    exact this x hx'
  have hNB' : N = B := (hsimple N hNB hNnorm).resolve_left hNne
  have hgen : ∀ x ∈ k, ∀ x' ∈ k, x * x' = x' * x := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    have h1 := hcon (y₁⁻¹ * y₂) (B.mul_mem (B.inv_mem hy₁) hy₂)
    have h2 := h1.map (MulAut.conj y₁).toMonoidHom
    have e1 : (MulAut.conj y₁).toMonoidHom l = y₁ * l * y₁⁻¹ := rfl
    have e2 : (MulAut.conj y₁).toMonoidHom ((y₁⁻¹ * y₂) * l * (y₁⁻¹ * y₂)⁻¹) =
        y₂ * l * y₂⁻¹ := by
      show y₁ * ((y₁⁻¹ * y₂) * l * (y₁⁻¹ * y₂)⁻¹) * y₁⁻¹ = y₂ * l * y₂⁻¹
      group
    rw [e1, e2] at h2
    exact h2.eq
  have hcomm1 : ∀ x₀ ∈ k, ∀ z ∈ N, z * x₀ = x₀ * z := by
    intro x₀ hx₀ z hz
    have : N ≤ Subgroup.centralizer ({x₀} : Set Γ) := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hgen x₀ hx₀ x hx
    have := Subgroup.mem_centralizer_iff.1 (this hz) x₀ (Set.mem_singleton _)
    exact this.symm
  have hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
    intro a ha b hb
    have : N ≤ Subgroup.centralizer ({a} : Set Γ) := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hcomm1 x hx a ha
    have := Subgroup.mem_centralizer_iff.1 (this hb) a (Set.mem_singleton _)
    exact this
  have hBle : B ≤ Subgroup.centralizer (B : Set Γ) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hNB'] at ha hb
    exact hcomm b hb a ha
  have hbot : ⁅B, B⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hBle
  exact hne (hperf.symm.trans hbot)

theorem commute_conj_iff {B D : Subgroup Γ} (hBD : B ≤ Subgroup.centralizer (D : Set Γ))
    {d l : Γ} (hd : d ∈ D) (hl : l ∈ B) (hdl : Commute d l) {y : Γ} (hy : y ∈ B) :
    Commute (d * l) (y * (d * l) * y⁻¹) ↔ Commute l (y * l * y⁻¹) := by
  have hyd : y * d = d * y := (Subgroup.mem_centralizer_iff.1 (hBD hy) d hd).symm
  have hyd' : y * d * y⁻¹ = d := by rw [hyd]; group
  have hl' : y * l * y⁻¹ ∈ B := B.mul_mem (B.mul_mem hy hl) (B.inv_mem hy)
  have hdl' : Commute d (y * l * y⁻¹) := Subgroup.mem_centralizer_iff.1 (hBD hl') d hd
  have e : y * (d * l) * y⁻¹ = d * (y * l * y⁻¹) := by
    calc y * (d * l) * y⁻¹ = (y * d * y⁻¹) * (y * l * y⁻¹) := by group
      _ = d * (y * l * y⁻¹) := by rw [hyd']
  rw [e]
  constructor
  · intro h
    have ha : Commute d⁻¹ (d * l) := ((Commute.refl d).mul_right hdl).inv_left
    have hb : Commute d⁻¹ (d * (y * l * y⁻¹)) := ((Commute.refl d).mul_right hdl').inv_left
    have h3 : Commute (d⁻¹ * (d * l)) (d⁻¹ * (d * (y * l * y⁻¹))) :=
      Commute.mul_left ((Commute.refl d⁻¹).mul_right hb) (ha.symm.mul_right h)
    simpa using h3
  · intro h
    exact Commute.mul_left ((Commute.refl d).mul_right hdl') (hdl.symm.mul_right h)

end Simple

section Central

variable {X : Type*} [Group X]

theorem eq_one_of_mem_center {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center X)) {z : X} (hz : z ∈ Subgroup.center X)
    (hzp : z ^ p = 1) : z = 1 := by
  have hord : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
  have hord2 : orderOf z ∣ Nat.card (Subgroup.center X) := Subgroup.orderOf_dvd_natCard _ hz
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center X)) := (hp.coprime_iff_not_dvd).2 hZ
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop hord hord2)

theorem commute_of_commutator_mem_center {p : ℕ} (hp : p.Prime)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center X)) {x y : X} (hx : x ^ p = 1)
    (hz : y * x * y⁻¹ * x⁻¹ ∈ Subgroup.center X) : y * x * y⁻¹ = x := by
  set z : X := y * x * y⁻¹ * x⁻¹ with hzdef
  have hzx : y * x * y⁻¹ = z * x := by rw [hzdef]; group
  have hzc : Commute z x := (Subgroup.mem_center_iff.1 hz x).symm
  have hpow : (y * x * y⁻¹) ^ p = 1 := by
    rw [conj_pow, hx]
    group
  have hzp : z ^ p = 1 := by
    have h1 : (z * x) ^ p = z ^ p * x ^ p := hzc.mul_pow p
    rw [← hzx, hpow, hx, mul_one] at h1
    exact h1.symm
  rw [hzx, eq_one_of_mem_center hp hZ hz hzp, one_mul]

end Central

end CFSG.RankThree.PartOne.Q1327Z
