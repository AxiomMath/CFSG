module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Quasithin

namespace G11

private theorem g119geom_add_self {F : Type*} [Field F] [CharP F 2] {U : Type*} [AddCommGroup U]
    [Module F U] (u : U) : u + u = 0 := by
  rw [← two_smul F u, CharTwo.two_eq_zero, zero_smul]

private def g119geom_T {F : Type*} [Field F] {U : Type*} [AddCommGroup U] [Module F U]
    {τ : F →+* F} (σ : U →ₛₗ[τ] U) {S : Submodule F U} (hS : ∀ s ∈ S, σ s ∈ S) (μ : F) :
    S →+ S where
  toFun s := ⟨(s : U) + μ • σ s, S.add_mem s.2 (S.smul_mem μ (hS _ s.2))⟩
  map_zero' := by ext; simp
  map_add' a b := by
    ext
    simp only [Submodule.coe_add, map_add, smul_add]
    abel

private theorem g119geom_T_coe {F : Type*} [Field F] {U : Type*} [AddCommGroup U] [Module F U]
    {τ : F →+* F} (σ : U →ₛₗ[τ] U) {S : Submodule F U} (hS : ∀ s ∈ S, σ s ∈ S) (μ : F)
    (s : S) : (g119geom_T σ hS μ s : U) = (s : U) + μ • σ s := rfl

private theorem g119geom_T_T {F : Type*} [Field F] [CharP F 2] {U : Type*} [AddCommGroup U]
    [Module F U] {τ : F →+* F} (σ : U →ₛₗ[τ] U) {S : Submodule F U} (hS : ∀ s ∈ S, σ s ∈ S)
    {μ n : F} (hμ : μ * τ μ * n = 1) (hsq : ∀ s ∈ S, σ (σ s) = n • s) (s : S) :
    g119geom_T σ hS μ (g119geom_T σ hS μ s) = 0 := by
  ext
  simp only [g119geom_T_coe, map_add, map_smulₛₗ, ZeroMemClass.coe_zero]
  rw [hsq _ s.2, smul_add, smul_smul, smul_smul, hμ, one_smul]
  have h2 := g119geom_add_self (F := F) (s : U)
  have h3 := g119geom_add_self (F := F) (μ • σ (s : U))
  calc (s : U) + μ • σ (s : U) + (μ • σ (s : U) + (s : U))
      = ((s : U) + (s : U)) + (μ • σ (s : U) + μ • σ (s : U)) := by abel
    _ = 0 := by rw [h2, h3, add_zero]

private theorem g119geom_card_le_sq {A : Type*} [AddCommGroup A] [Finite A] (T : A →+ A)
    (hT : ∀ a, T (T a) = 0) : Nat.card A ≤ Nat.card T.ker ^ 2 := by
  have h1 : Nat.card A = Nat.card (A ⧸ T.ker) * Nat.card T.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup T.ker
  have h2 : Nat.card (A ⧸ T.ker) = Nat.card T.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange T).toEquiv
  have h3 : T.range ≤ T.ker := by
    rintro _ ⟨a, rfl⟩
    exact hT a
  have h4 : Nat.card T.range ≤ Nat.card T.ker := AddSubgroup.card_le_of_le h3
  rw [h1, h2, sq]
  exact Nat.mul_le_mul_right _ h4

theorem g119_exists_second_eigenline {F : Type*} [Field F] [Finite F] [CharP F 2]
    {U : Type*} [AddCommGroup U] [Module F U] [Module.Finite F U]
    (τ : F →+* F) (σ : U →ₛₗ[τ] U) (hσ : Function.Injective σ)
    {S : Submodule F U} (hS : ∀ s ∈ S, σ s ∈ S)
    (hinv : ∀ s ∈ S, ∃ c : F, σ (σ s) = c • s) (hdim : 3 ≤ Module.finrank F S)
    {v₀ : U} (hv₀ : v₀ ∈ S) (hv₀0 : v₀ ≠ 0) {c₀ : F} (hfix : σ v₀ = c₀ • v₀) :
    ∃ v ∈ S, v ∉ Submodule.span F {v₀} ∧ ∃ c : F, σ v = c • v := by
  classical
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    refine hv₀0 (hσ ?_)
    rw [hfix, zero_smul, map_zero]
  have hτc₀ : τ c₀ ≠ 0 := (map_ne_zero τ).2 hc₀
  have hσσv₀ : σ (σ v₀) = (τ c₀ * c₀) • v₀ := by
    rw [hfix, map_smulₛₗ, hfix, smul_smul]
  obtain ⟨u, huS, hun⟩ : ∃ u ∈ S, u ∉ Submodule.span F {v₀} := by
    by_contra hcon
    have hle : S ≤ Submodule.span F {v₀} := fun s hs => by
      by_contra hs'
      exact hcon ⟨s, hs, hs'⟩
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hv₀0] at h1
    omega
  have hoff : ∀ s ∈ S, s ∉ Submodule.span F {v₀} → σ (σ s) = (τ c₀ * c₀) • s := by
    intro s hs hsn
    obtain ⟨c1, hc1⟩ := hinv (s + v₀) (S.add_mem hs hv₀)
    obtain ⟨cs, hcs⟩ := hinv s hs
    rw [map_add, map_add, hcs, hσσv₀, smul_add] at hc1
    have key : (c1 - cs) • s = ((τ c₀ * c₀) - c1) • v₀ := by
      rw [sub_smul, sub_smul]
      calc c1 • s - cs • s = (c1 • s + c1 • v₀) - (cs • s + c1 • v₀) := by abel
        _ = (cs • s + (τ c₀ * c₀) • v₀) - (cs • s + c1 • v₀) := by rw [hc1]
        _ = (τ c₀ * c₀) • v₀ - c1 • v₀ := by abel
    by_cases h : c1 = cs
    · subst h
      have h0 : ((τ c₀ * c₀) - c1) • v₀ = 0 := by rw [← key]; simp
      rcases smul_eq_zero.1 h0 with h0 | h0
      · rw [hcs, sub_eq_zero.1 h0]
      · exact absurd h0 hv₀0
    · exfalso
      apply hsn
      have hs' : s = (c1 - cs)⁻¹ • (((τ c₀ * c₀) - c1) • v₀) := by
        rw [← key, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 h), one_smul]
      rw [hs']
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v₀))
  have hsq : ∀ s ∈ S, σ (σ s) = (τ c₀ * c₀) • s := by
    intro s hs
    by_cases hsn : s ∈ Submodule.span F {v₀}
    · have hsu : s + u ∉ Submodule.span F {v₀} := fun h => hun (by simpa using sub_mem h hsn)
      have h1 := hoff (s + u) (S.add_mem hs huS) hsu
      have h2 := hoff u huS hun
      rw [map_add, map_add, h2, smul_add] at h1
      exact add_right_cancel h1
    · exact hoff s hs hsn
  have hμ : c₀⁻¹ * τ c₀⁻¹ * (τ c₀ * c₀) = 1 := by
    rw [map_inv₀]
    field_simp
  have : Finite S := Module.finite_of_finite F
  have : Finite (Submodule.span F {v₀}) := Module.finite_of_finite F
  let T := g119geom_T σ hS c₀⁻¹
  have hT : ∀ s, T (T s) = 0 := g119geom_T_T σ hS hμ hsq
  have hcard : Nat.card S ≤ Nat.card T.ker ^ 2 := g119geom_card_le_sq T hT
  by_contra hcon
  have hker : ∀ s : S, s ∈ T.ker → (s : U) ∈ Submodule.span F {v₀} := by
    intro s hs
    by_contra hns
    refine hcon ⟨s, s.2, hns, c₀, ?_⟩
    have h0 : (s : U) + c₀⁻¹ • σ (s : U) = 0 := by
      have := congrArg (fun x : S => (x : U)) (AddMonoidHom.mem_ker.1 hs)
      exact this
    have h1 : c₀ • (s : U) + σ (s : U) = 0 := by
      have := congrArg (fun x : U => c₀ • x) h0
      simpa [smul_add, smul_smul, mul_inv_cancel₀ hc₀] using this
    have h2 : σ (s : U) = -(c₀ • (s : U)) := eq_neg_of_add_eq_zero_right h1
    rw [h2, ← neg_smul, CharTwo.neg_eq]
  have hle : Nat.card T.ker ≤ Nat.card F := by
    have hinj : Function.Injective
        (fun k : T.ker => (⟨((k : S) : U), hker k k.2⟩ : Submodule.span F {v₀})) := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hab
    have h1 := Nat.card_le_card_of_injective _ hinj
    rwa [Module.natCard_eq_pow_finrank (K := F) (V := Submodule.span F {v₀}),
      finrank_span_singleton hv₀0, pow_one] at h1
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hS3 : Nat.card F ^ 3 ≤ Nat.card S := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := S)]
    exact Nat.pow_le_pow_right (by omega) hdim
  have h32 : Nat.card F ^ 3 ≤ Nat.card F ^ 2 :=
    calc Nat.card F ^ 3 ≤ Nat.card S := hS3
      _ ≤ Nat.card T.ker ^ 2 := hcard
      _ ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hle 2
  have h23 : Nat.card F ^ 2 < Nat.card F ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
  omega

end G11

end CFSG.Quasithin
