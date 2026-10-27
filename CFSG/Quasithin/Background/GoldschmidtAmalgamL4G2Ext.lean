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
public import Mathlib.Order.CompletePartialOrder
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

namespace CFSG.Quasithin.F6.GoldAmL4

variable {D E : Type*} [Group D] [Group E]

@[expose] def twoExt (A : Subgroup D) (ρ : D) (hρ : ρ * ρ = 1) (hn : ∀ g ∈ A, ρ * g * ρ ∈ A) :
    Subgroup D where
  carrier := {g | g ∈ A ∨ g * ρ ∈ A}
  mul_mem' := by
    rintro g k (hg | hg) (hk | hk)
    · exact Or.inl (A.mul_mem hg hk)
    · refine Or.inr ?_
      rw [mul_assoc]
      exact A.mul_mem hg hk
    · refine Or.inr ?_
      have := A.mul_mem hg (hn k hk)
      have e : g * ρ * (ρ * k * ρ) = g * k * ρ := by
        calc g * ρ * (ρ * k * ρ) = g * (ρ * ρ) * k * ρ := by group
          _ = g * k * ρ := by rw [hρ]; group
      rwa [e] at this
    · refine Or.inl ?_
      have := A.mul_mem hg (hn _ hk)
      have e : g * ρ * (ρ * (k * ρ) * ρ) = g * k := by
        calc g * ρ * (ρ * (k * ρ) * ρ) = g * (ρ * ρ) * k * (ρ * ρ) := by group
          _ = g * k := by rw [hρ]; group
      rwa [e] at this
  one_mem' := Or.inl A.one_mem
  inv_mem' := by
    rintro g (hg | hg)
    · exact Or.inl (A.inv_mem hg)
    · refine Or.inr ?_
      have h1 : ρ * g⁻¹ ∈ A := by
        have := A.inv_mem hg
        have e : (g * ρ)⁻¹ = ρ * g⁻¹ := by
          have : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ
          rw [mul_inv_rev, this]
        rwa [e] at this
      have := hn _ h1
      have e : ρ * (ρ * g⁻¹) * ρ = g⁻¹ * ρ := by
        calc ρ * (ρ * g⁻¹) * ρ = (ρ * ρ) * g⁻¹ * ρ := by group
          _ = g⁻¹ * ρ := by rw [hρ]; group
      rwa [e] at this

theorem closure_union_eq {A : Subgroup D} {ρ : D} (hρ : ρ * ρ = 1)
    (hn : ∀ g ∈ A, ρ * g * ρ ∈ A) :
    Subgroup.closure ((A : Set D) ∪ {ρ}) = twoExt A ρ hρ hn := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro g (hg | hg)
    · exact Or.inl hg
    · rw [Set.mem_singleton_iff] at hg
      subst hg
      exact Or.inr (by rw [hρ]; exact A.one_mem)
  · rintro g (hg | hg)
    · exact Subgroup.subset_closure (Or.inl hg)
    · have h1 : g * ρ ∈ Subgroup.closure ((A : Set D) ∪ {ρ}) :=
        Subgroup.subset_closure (Or.inl hg)
      have h2 : ρ ∈ Subgroup.closure ((A : Set D) ∪ {ρ}) := Subgroup.subset_closure (Or.inr rfl)
      have := Subgroup.mul_mem _ h1 h2
      have e : g * ρ * ρ = g := by rw [mul_assoc, hρ, mul_one]
      rwa [e] at this

theorem normalizes_of_gens {S : Set D} {A : Subgroup D} (hA : A = Subgroup.closure S) {ρ : D}
    (hρ : ρ * ρ = 1) (hgen : ∀ g ∈ S, ρ * g * ρ ∈ A) : ∀ g ∈ A, ρ * g * ρ ∈ A := by
  intro g hg
  subst hA
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hgen x hx
  | one => simp [hρ]
  | mul x y hx hy ihx ihy =>
    have := Subgroup.mul_mem _ ihx ihy
    have e : ρ * x * ρ * (ρ * y * ρ) = ρ * (x * y) * ρ := by
      calc ρ * x * ρ * (ρ * y * ρ) = ρ * x * (ρ * ρ) * y * ρ := by group
        _ = ρ * (x * y) * ρ := by rw [hρ]; group
    rwa [e] at this
  | inv x hx ih =>
    have := Subgroup.inv_mem _ ih
    have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ
    have e : (ρ * x * ρ)⁻¹ = ρ * x⁻¹ * ρ := by
      rw [mul_inv_rev, mul_inv_rev, hρinv]; group
    rwa [e] at this

variable {A : Subgroup D} {A' : Subgroup E} {ρ : D} {ρ' : E}

theorem exists_mulEquiv_two (hρ : ρ * ρ = 1) (hρ' : ρ' * ρ' = 1)
    (hn : ∀ g ∈ A, ρ * g * ρ ∈ A) (hn' : ∀ g ∈ A', ρ' * g * ρ' ∈ A')
    (hρA : ρ ∉ A) (hρA' : ρ' ∉ A') (φ : ↥A ≃* ↥A')
    (hφ : ∀ (g : D) (hg : g ∈ A),
      ((φ ⟨ρ * g * ρ, hn g hg⟩ : ↥A') : E) = ρ' * ((φ ⟨g, hg⟩ : ↥A') : E) * ρ') :
    ∃ Φ : ↥(Subgroup.closure ((A : Set D) ∪ {ρ})) ≃*
        ↥(Subgroup.closure ((A' : Set E) ∪ {ρ'})),
      (∀ (g : D) (hg : g ∈ A),
        ((Φ ⟨g, Subgroup.subset_closure (Or.inl hg)⟩ :
          ↥(Subgroup.closure ((A' : Set E) ∪ {ρ'}))) : E) = ((φ ⟨g, hg⟩ : ↥A') : E)) ∧
      ((Φ ⟨ρ, Subgroup.subset_closure (Or.inr rfl)⟩ :
        ↥(Subgroup.closure ((A' : Set E) ∪ {ρ'}))) : E) = ρ' := by
  classical
  have e1 := closure_union_eq hρ hn
  have e2 := closure_union_eq hρ' hn'
  set H := twoExt A ρ hρ hn with hH
  set H' := twoExt A' ρ' hρ' hn' with hH'
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ
  have hρ'inv : ρ'⁻¹ = ρ' := inv_eq_of_mul_eq_one_right hρ'
  let F : D → E := fun g =>
    if hg : g ∈ A then ((φ ⟨g, hg⟩ : ↥A') : E)
    else if hg' : g * ρ ∈ A then ((φ ⟨g * ρ, hg'⟩ : ↥A') : E) * ρ' else 1
  have hF1 : ∀ (g : D) (hg : g ∈ A), F g = ((φ ⟨g, hg⟩ : ↥A') : E) := fun g hg => by
    simp only [F, hg, ↓reduceDIte]
  have hF2 : ∀ (g : D) (hg : g ∉ A) (hg' : g * ρ ∈ A),
      F g = ((φ ⟨g * ρ, hg'⟩ : ↥A') : E) * ρ' := fun g hg hg' => by
    simp only [F, hg, hg', ↓reduceDIte]
  have hex : ∀ g : D, g ∈ A → g * ρ ∈ A → False := fun g hg hg' => hρA (by
    have := A.mul_mem (A.inv_mem hg) hg'
    simpa using this)
  have hmemA' : ∀ (g : D) (hg : g ∈ A), F g ∈ A' := fun g hg => by
    rw [hF1 g hg]; exact (φ ⟨g, hg⟩).2
  have hFρ : ∀ (g : D) (hg : g * ρ ∈ A), F g = ((φ ⟨g * ρ, hg⟩ : ↥A') : E) * ρ' := by
    intro g hg
    by_cases hgA : g ∈ A
    · exact absurd hg (fun h => hex g hgA h)
    · exact hF2 g hgA hg
  have hmul : ∀ g ∈ H, ∀ k ∈ H, F (g * k) = F g * F k := by
    intro g hg k hk
    rcases hg with hg | hg <;> rcases hk with hk | hk
    · rw [hF1 g hg, hF1 k hk, hF1 (g * k) (A.mul_mem hg hk)]
      exact congrArg Subtype.val (map_mul φ ⟨g, hg⟩ ⟨k, hk⟩)
    ·
      have h1 : g * k * ρ ∈ A := by rw [mul_assoc]; exact A.mul_mem hg hk
      rw [hFρ (g * k) h1, hF1 g hg, hFρ k hk]
      have : (⟨g * k * ρ, h1⟩ : ↥A) = ⟨g, hg⟩ * ⟨k * ρ, hk⟩ := by
        apply Subtype.ext; simp [mul_assoc]
      rw [this, map_mul]
      simp [mul_assoc]
    ·
      have h2 : ρ * k * ρ ∈ A := hn k hk
      have h1 : g * k * ρ ∈ A := by
        have := A.mul_mem hg h2
        have e : g * ρ * (ρ * k * ρ) = g * k * ρ := by
          calc g * ρ * (ρ * k * ρ) = g * (ρ * ρ) * k * ρ := by group
            _ = g * k * ρ := by rw [hρ]; group
        rwa [e] at this
      rw [hFρ (g * k) h1, hFρ g hg, hF1 k hk]
      have : (⟨g * k * ρ, h1⟩ : ↥A) = ⟨g * ρ, hg⟩ * ⟨ρ * k * ρ, h2⟩ := by
        apply Subtype.ext
        show g * k * ρ = g * ρ * (ρ * k * ρ)
        calc g * k * ρ = g * (ρ * ρ) * k * ρ := by rw [hρ]; group
          _ = g * ρ * (ρ * k * ρ) := by group
      rw [this, map_mul, Subgroup.coe_mul, hφ k hk]
      calc ((φ ⟨g * ρ, hg⟩ : ↥A') : E) * (ρ' * ((φ ⟨k, hk⟩ : ↥A') : E) * ρ') * ρ'
          = ((φ ⟨g * ρ, hg⟩ : ↥A') : E) * ρ' * ((φ ⟨k, hk⟩ : ↥A') : E) * (ρ' * ρ') := by group
        _ = _ := by rw [hρ']; simp
    ·
      have h2 : ρ * (k * ρ) * ρ ∈ A := hn _ hk
      have h1 : g * k ∈ A := by
        have := A.mul_mem hg h2
        have e : g * ρ * (ρ * (k * ρ) * ρ) = g * k := by
          calc g * ρ * (ρ * (k * ρ) * ρ) = g * (ρ * ρ) * k * (ρ * ρ) := by group
            _ = g * k := by rw [hρ]; group
        rwa [e] at this
      rw [hF1 (g * k) h1, hFρ g hg, hFρ k hk]
      have : (⟨g * k, h1⟩ : ↥A) = ⟨g * ρ, hg⟩ * ⟨ρ * (k * ρ) * ρ, h2⟩ := by
        apply Subtype.ext
        show g * k = g * ρ * (ρ * (k * ρ) * ρ)
        calc g * k = g * (ρ * ρ) * k * (ρ * ρ) := by rw [hρ]; group
          _ = g * ρ * (ρ * (k * ρ) * ρ) := by group
      rw [this, map_mul, Subgroup.coe_mul, hφ (k * ρ) hk]
      simp [mul_assoc]
  have hmem : ∀ g ∈ H, F g ∈ H' := by
    rintro g (hg | hg)
    · exact Or.inl (hmemA' g hg)
    · rw [hFρ g hg]
      refine Or.inr ?_
      rw [mul_assoc, hρ', mul_one]
      exact (φ ⟨g * ρ, hg⟩).2
  have hone : F 1 = 1 := by
    rw [hF1 1 A.one_mem]
    exact congrArg Subtype.val (map_one φ)
  let Φ₀ : ↥H →* ↥H' :=
    { toFun := fun g => ⟨F g, hmem g g.2⟩
      map_one' := Subtype.ext hone
      map_mul' := fun g k => Subtype.ext (hmul g g.2 k k.2) }
  have hinj : Function.Injective Φ₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hg1 : F g = 1 := congrArg Subtype.val hg
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rcases g.2 with hgA | hgA
    · rw [hF1 g hgA] at hg1
      have : (⟨g, hgA⟩ : ↥A) = 1 := φ.injective (Subtype.ext (by simpa using hg1))
      simpa using congrArg Subtype.val this
    · exfalso
      rw [hFρ g hgA] at hg1
      apply hρA'
      have : ρ' = (((φ ⟨g * ρ, hgA⟩ : ↥A') : E))⁻¹ := eq_inv_of_mul_eq_one_right hg1
      rw [this]
      exact A'.inv_mem (φ ⟨g * ρ, hgA⟩).2
  have hsurj : Function.Surjective Φ₀ := by
    intro g'
    rcases g'.2 with hg' | hg'
    · refine ⟨⟨(φ.symm ⟨g', hg'⟩ : ↥A), Or.inl (φ.symm ⟨g', hg'⟩).2⟩, Subtype.ext ?_⟩
      show F ((φ.symm ⟨g', hg'⟩ : ↥A) : D) = g'
      rw [hF1 _ (φ.symm ⟨g', hg'⟩).2]
      simp
    ·
      set u : D := ((φ.symm ⟨g' * ρ', hg'⟩ : ↥A) : D) with hu
      have huA : u ∈ A := (φ.symm ⟨g' * ρ', hg'⟩).2
      have hu' : u * ρ * ρ ∈ A := by rw [mul_assoc, hρ, mul_one]; exact huA
      have hmemH : u * ρ ∈ H := Or.inr hu'
      refine ⟨⟨u * ρ, hmemH⟩, Subtype.ext ?_⟩
      show F (u * ρ) = g'
      rw [hFρ (u * ρ) hu']
      have e1 : (⟨u * ρ * ρ, hu'⟩ : ↥A) = ⟨u, huA⟩ := by
        apply Subtype.ext; show u * ρ * ρ = u; rw [mul_assoc, hρ, mul_one]
      rw [e1]
      have e2 : (φ ⟨u, huA⟩ : ↥A') = ⟨g' * ρ', hg'⟩ := by
        have : (⟨u, huA⟩ : ↥A) = φ.symm ⟨g' * ρ', hg'⟩ := rfl
        rw [this]; simp
      rw [e2]
      show g' * ρ' * ρ' = g'
      rw [mul_assoc, hρ', mul_one]
  let Ψ : ↥H ≃* ↥H' := MulEquiv.ofBijective Φ₀ ⟨hinj, hsurj⟩
  refine ⟨(MulEquiv.subgroupCongr e1).trans (Ψ.trans (MulEquiv.subgroupCongr e2.symm)),
    fun g hg => ?_, ?_⟩
  · show F g = _
    exact hF1 g hg
  · show F ρ = ρ'
    have hρ1 : ρ * ρ ∈ A := by rw [hρ]; exact A.one_mem
    rw [hFρ ρ hρ1]
    have : (⟨ρ * ρ, hρ1⟩ : ↥A) = 1 := Subtype.ext hρ
    rw [this, map_one]
    simp

theorem compat_of_gens {S : Set D} (hA : A = Subgroup.closure S) (hρ : ρ * ρ = 1)
    (hρ' : ρ' * ρ' = 1) (hn : ∀ g ∈ A, ρ * g * ρ ∈ A) (φ : ↥A ≃* ↥A')
    (hgen : ∀ (g : D) (hg : g ∈ A), g ∈ S →
      ((φ ⟨ρ * g * ρ, hn g hg⟩ : ↥A') : E) = ρ' * ((φ ⟨g, hg⟩ : ↥A') : E) * ρ') :
    ∀ (g : D) (hg : g ∈ A),
      ((φ ⟨ρ * g * ρ, hn g hg⟩ : ↥A') : E) = ρ' * ((φ ⟨g, hg⟩ : ↥A') : E) * ρ' := by
  have hρinv : ρ⁻¹ = ρ := inv_eq_of_mul_eq_one_right hρ
  have hρ'inv : ρ'⁻¹ = ρ' := inv_eq_of_mul_eq_one_right hρ'
  intro g hg
  have hgS : g ∈ Subgroup.closure S := hA ▸ hg
  induction hgS using Subgroup.closure_induction with
  | mem x hx => exact hgen x (hA ▸ Subgroup.subset_closure hx) hx
  | one =>
    have e1 : (⟨ρ * 1 * ρ, hn 1 A.one_mem⟩ : ↥A) = 1 := Subtype.ext (by simp [hρ])
    have e2 : (⟨1, A.one_mem⟩ : ↥A) = 1 := rfl
    rw [e1, e2, map_one]
    simp [hρ']
  | mul x y hx hy ihx ihy =>
    have hxA : x ∈ A := hA ▸ hx
    have hyA : y ∈ A := hA ▸ hy
    have e : (⟨ρ * (x * y) * ρ, hn _ (A.mul_mem hxA hyA)⟩ : ↥A) =
        ⟨ρ * x * ρ, hn x hxA⟩ * ⟨ρ * y * ρ, hn y hyA⟩ := by
      apply Subtype.ext
      show ρ * (x * y) * ρ = ρ * x * ρ * (ρ * y * ρ)
      calc ρ * (x * y) * ρ = ρ * x * (ρ * ρ) * y * ρ := by rw [hρ]; group
        _ = ρ * x * ρ * (ρ * y * ρ) := by group
    have e2 : (⟨x * y, A.mul_mem hxA hyA⟩ : ↥A) = ⟨x, hxA⟩ * ⟨y, hyA⟩ := rfl
    rw [e, map_mul, Subgroup.coe_mul, ihx hxA, ihy hyA, e2, map_mul, Subgroup.coe_mul]
    calc ρ' * ((φ ⟨x, hxA⟩ : ↥A') : E) * ρ' * (ρ' * ((φ ⟨y, hyA⟩ : ↥A') : E) * ρ')
        = ρ' * ((φ ⟨x, hxA⟩ : ↥A') : E) * (ρ' * ρ') * ((φ ⟨y, hyA⟩ : ↥A') : E) * ρ' := by group
      _ = ρ' * (((φ ⟨x, hxA⟩ : ↥A') : E) * ((φ ⟨y, hyA⟩ : ↥A') : E)) * ρ' := by
        rw [hρ']; group
  | inv x hx ih =>
    have hxA : x ∈ A := hA ▸ hx
    have e : (⟨ρ * x⁻¹ * ρ, hn _ (A.inv_mem hxA)⟩ : ↥A) = (⟨ρ * x * ρ, hn x hxA⟩ : ↥A)⁻¹ := by
      apply Subtype.ext
      show ρ * x⁻¹ * ρ = (ρ * x * ρ)⁻¹
      rw [mul_inv_rev, mul_inv_rev, hρinv]; group
    have e2 : (⟨x⁻¹, A.inv_mem hxA⟩ : ↥A) = (⟨x, hxA⟩ : ↥A)⁻¹ := rfl
    rw [e, map_inv, Subgroup.coe_inv, ih hxA, e2, map_inv, Subgroup.coe_inv]
    rw [mul_inv_rev, mul_inv_rev, hρ'inv]; group

theorem compat_gen_aux (hn : ∀ g ∈ A, ρ * g * ρ ∈ A) (φ : ↥A ≃* ↥A') {g h : D} (hg : g ∈ A)
    (hh : h ∈ A) (e : ρ * g * ρ = h) {g' h' : E} (hφg : ((φ ⟨g, hg⟩ : ↥A') : E) = g')
    (hφh : ((φ ⟨h, hh⟩ : ↥A') : E) = h') (e' : ρ' * g' * ρ' = h') :
    ((φ ⟨ρ * g * ρ, hn g hg⟩ : ↥A') : E) = ρ' * ((φ ⟨g, hg⟩ : ↥A') : E) * ρ' := by
  have : (⟨ρ * g * ρ, hn g hg⟩ : ↥A) = ⟨h, hh⟩ := Subtype.ext e
  rw [this, hφh, hφg, e']

theorem closure_union_closure (S : Set D) (ρ : D) :
    Subgroup.closure (S ∪ {ρ}) = Subgroup.closure ((Subgroup.closure S : Set D) ∪ {ρ}) := by
  rw [Subgroup.closure_union, Subgroup.closure_union, Subgroup.closure_eq]

theorem exists_vertex_ext {S : Set D} {S' : Set E} {B : Subgroup D} {B' : Subgroup E}
    (hB : B = Subgroup.closure S) (hB' : B' = Subgroup.closure S') (hρ : ρ * ρ = 1)
    (hρ' : ρ' * ρ' = 1) (hgen : ∀ g ∈ S, ρ * g * ρ ∈ B) (hgen' : ∀ g ∈ S', ρ' * g * ρ' ∈ B')
    (hρB : ρ ∉ B) (hρB' : ρ' ∉ B') (φ : ↥B ≃* ↥B')
    (hφ : ∀ (g : D) (hg : g ∈ B), g ∈ S →
      ((φ ⟨ρ * g * ρ, normalizes_of_gens hB hρ hgen g hg⟩ : ↥B') : E) =
        ρ' * ((φ ⟨g, hg⟩ : ↥B') : E) * ρ') :
    ∃ Φ : ↥(Subgroup.closure ((B : Set D) ∪ {ρ})) ≃* ↥(Subgroup.closure ((B' : Set E) ∪ {ρ'})),
      (∀ (g : D) (hg : g ∈ B),
        ((Φ ⟨g, Subgroup.subset_closure (Or.inl hg)⟩ :
          ↥(Subgroup.closure ((B' : Set E) ∪ {ρ'}))) : E) = ((φ ⟨g, hg⟩ : ↥B') : E)) ∧
      ((Φ ⟨ρ, Subgroup.subset_closure (Or.inr rfl)⟩ :
        ↥(Subgroup.closure ((B' : Set E) ∪ {ρ'}))) : E) = ρ' :=
  exists_mulEquiv_two hρ hρ' (normalizes_of_gens hB hρ hgen) (normalizes_of_gens hB' hρ' hgen')
    hρB hρB' φ (compat_of_gens hB hρ hρ' (normalizes_of_gens hB hρ hgen) φ hφ)

end CFSG.Quasithin.F6.GoldAmL4
