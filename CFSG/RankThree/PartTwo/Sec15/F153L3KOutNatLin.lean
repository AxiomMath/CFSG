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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

open scoped MatrixGroups Matrix

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatB

open Matrix

theorem dot_vecCons3 {F : Type} [Field F] (p q r : F) (u : Fin 3 → F) :
    (![p, q, r] : Fin 3 → F) ⬝ᵥ u = p * u 0 + q * u 1 + r * u 2 := by
  simp [dotProduct, Fin.sum_univ_three]

theorem exists_two_functionals {F : Type} [Field F] (v : Fin 3 → F) (hv : v ≠ 0) :
    ∃ φ₁ φ₂ : Fin 3 → F, φ₁ ≠ 0 ∧ φ₂ ≠ 0 ∧ φ₁ ⬝ᵥ v = 0 ∧ φ₂ ⬝ᵥ v = 0 ∧
      ∀ u : Fin 3 → F, φ₁ ⬝ᵥ u = 0 → φ₂ ⬝ᵥ u = 0 → ∃ c : F, u = c • v := by
  have hcase : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hv
    funext i
    fin_cases i
    · simpa using hne.1
    · simpa using hne.2.1
    · simpa using hne.2.2
  rcases hcase with h0 | h1 | h2
  · refine ⟨![-v 1, v 0, 0], ![-v 2, 0, v 0], ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact h0 (by simpa using congrFun h 1)
    · intro h
      exact h0 (by simpa using congrFun h 2)
    · rw [dot_vecCons3]
      ring
    · rw [dot_vecCons3]
      ring
    · intro u hu1 hu2
      rw [dot_vecCons3] at hu1 hu2
      have e1 : u 1 = u 0 / v 0 * v 1 := by
        rw [div_mul_eq_mul_div, eq_div_iff h0]
        linear_combination hu1
      have e2 : u 2 = u 0 / v 0 * v 2 := by
        rw [div_mul_eq_mul_div, eq_div_iff h0]
        linear_combination hu2
      refine ⟨u 0 / v 0, ?_⟩
      funext i
      fin_cases i
      · simp [h0]
      · simp [e1]
      · simp [e2]
  · refine ⟨![v 1, -v 0, 0], ![0, -v 2, v 1], ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact h1 (by simpa using congrFun h 0)
    · intro h
      exact h1 (by simpa using congrFun h 2)
    · rw [dot_vecCons3]
      ring
    · rw [dot_vecCons3]
      ring
    · intro u hu1 hu2
      rw [dot_vecCons3] at hu1 hu2
      have e0 : u 0 = u 1 / v 1 * v 0 := by
        rw [div_mul_eq_mul_div, eq_div_iff h1]
        linear_combination hu1
      have e2 : u 2 = u 1 / v 1 * v 2 := by
        rw [div_mul_eq_mul_div, eq_div_iff h1]
        linear_combination hu2
      refine ⟨u 1 / v 1, ?_⟩
      funext i
      fin_cases i
      · simp [e0]
      · simp [h1]
      · simp [e2]
  · refine ⟨![v 2, 0, -v 0], ![0, v 2, -v 1], ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact h2 (by simpa using congrFun h 0)
    · intro h
      exact h2 (by simpa using congrFun h 1)
    · rw [dot_vecCons3]
      ring
    · rw [dot_vecCons3]
      ring
    · intro u hu1 hu2
      rw [dot_vecCons3] at hu1 hu2
      have e0 : u 0 = u 2 / v 2 * v 0 := by
        rw [div_mul_eq_mul_div, eq_div_iff h2]
        linear_combination hu1
      have e1 : u 1 = u 2 / v 2 * v 1 := by
        rw [div_mul_eq_mul_div, eq_div_iff h2]
        linear_combination hu2
      refine ⟨u 2 / v 2, ?_⟩
      funext i
      fin_cases i
      · simp [e0]
      · simp [e1]
      · simp [h2]

theorem lines_fixed_of_flag {F : Type} [Field F] (a : (Fin 3 → F) ≃+ (Fin 3 → F))
    (hflag : ∀ v φ : Fin 3 → F, v ≠ 0 → φ ≠ 0 → φ ⬝ᵥ v = 0 →
      (∀ c : F, ∃ c' : F, a (c • v) = c' • v) ∨ (∀ u, φ ⬝ᵥ u = 0 → φ ⬝ᵥ a u = 0)) :
    ∀ v : Fin 3 → F, ∃ μ : F, a v = μ • v := by
  intro v
  by_cases hv : v = 0
  · exact ⟨0, by subst hv; simp⟩
  obtain ⟨φ₁, φ₂, hφ₁, hφ₂, hφ₁v, hφ₂v, hker⟩ := exists_two_functionals v hv
  rcases hflag v φ₁ hv hφ₁ hφ₁v with h1 | h1
  · obtain ⟨c', hc'⟩ := h1 1
    exact ⟨c', by simpa using hc'⟩
  · rcases hflag v φ₂ hv hφ₂ hφ₂v with h2 | h2
    · obtain ⟨c', hc'⟩ := h2 1
      exact ⟨c', by simpa using hc'⟩
    · obtain ⟨c, hc⟩ := hker (a v) (h1 v hφ₁v) (h2 v hφ₂v)
      exact ⟨c, hc⟩

theorem scalar_of_lines_fixed {F : Type} [Field F] (a : (Fin 3 → F) ≃+ (Fin 3 → F))
    (h : ∀ v : Fin 3 → F, ∃ μ : F, a v = μ • v) : ∃ «λ» : F, ∀ v, a v = «λ» • v := by
  have indep : ∀ v w : Fin 3 → F, ∀ μ ν : F, v ≠ 0 → (∀ c : F, w ≠ c • v) →
      a v = μ • v → a w = ν • w → μ = ν := by
    intro v w μ ν hv hw hμ hν
    obtain ⟨ρ, hρ⟩ := h (v + w)
    have key : (μ - ρ) • v + (ν - ρ) • w = 0 := by
      rw [map_add, hμ, hν, smul_add] at hρ
      rw [sub_smul, sub_smul]
      calc μ • v - ρ • v + (ν • w - ρ • w) = (μ • v + ν • w) - (ρ • v + ρ • w) := by abel
        _ = 0 := by rw [hρ, sub_self]
    by_cases hβ : ν - ρ = 0
    · rw [hβ, zero_smul, add_zero] at key
      rcases smul_eq_zero.mp key with hα | hα
      · linear_combination hα - hβ
      · exact absurd hα hv
    · exfalso
      have h3 : (ν - ρ) • w = (-(μ - ρ)) • v := by
        rw [neg_smul]
        exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact key)
      have hw' : w = (-(μ - ρ) / (ν - ρ)) • v := by
        calc w = (ν - ρ)⁻¹ • ((ν - ρ) • w) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
          _ = (ν - ρ)⁻¹ • ((-(μ - ρ)) • v) := by rw [h3]
          _ = (-(μ - ρ) / (ν - ρ)) • v := by rw [smul_smul, div_eq_inv_mul]
      exact hw _ hw'
  obtain ⟨lam, hlam⟩ := h ![1, 0, 0]
  refine ⟨lam, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv
    simp
  obtain ⟨μ, hμ⟩ := h v
  have he₀ : (![1, 0, 0] : Fin 3 → F) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp at this
  have he₁ : (![0, 1, 0] : Fin 3 → F) ≠ 0 := by
    intro h0
    have := congrFun h0 1
    simp at this
  suffices hsuff : μ = lam by rw [hμ, hsuff]
  by_cases hc : ∃ c : F, v = c • ![1, 0, 0]
  · obtain ⟨c, hc⟩ := hc
    obtain ⟨ν, hν⟩ := h ![0, 1, 0]
    have hw1 : ∀ d : F, (![0, 1, 0] : Fin 3 → F) ≠ d • ![1, 0, 0] := by
      intro d hd
      have := congrFun hd 1
      simp at this
    have hw2 : ∀ d : F, v ≠ d • ![0, 1, 0] := by
      intro d hd
      apply hv
      have h0 : v 0 = 0 := by
        have := congrFun hd 0
        simpa using this
      have hc0 : c = 0 := by
        have := congrFun hc 0
        simp at this
        rw [← this]
        exact h0
      rw [hc, hc0, zero_smul]
    have h01 : lam = ν := indep _ _ _ _ he₀ hw1 hlam hν
    have h12 : ν = μ := indep _ _ _ _ he₁ hw2 hν hμ
    exact (h01.trans h12).symm
  · push Not at hc
    exact (indep _ _ _ _ he₀ hc hlam hμ).symm

theorem eq_id_of_lines_fixed {F : Type} [Field F] [CharP F 2] (a : (Fin 3 → F) ≃+ (Fin 3 → F))
    (ha : ∀ u, a (a u) = u) (h : ∀ v : Fin 3 → F, ∃ μ : F, a v = μ • v) : ∀ v, a v = v := by
  obtain ⟨lam, hlam⟩ := scalar_of_lines_fixed a h
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have h1 : lam • (lam • (![1, 0, 0] : Fin 3 → F)) = ![1, 0, 0] := by
    rw [← hlam ![1, 0, 0], ← hlam (a ![1, 0, 0])]
    exact ha _
  rw [smul_smul] at h1
  have hsq : lam * lam = 1 := by
    have := congrFun h1 0
    simpa using this
  have h3 : (lam - 1) * (lam - 1) = 0 := by
    linear_combination hsq + (1 - lam) * h2
  have h5 : lam = 1 := sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  intro v
  rw [hlam v, h5, one_smul]

end CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatB

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatA

open Matrix

theorem exists_dot_eq {F : Type} [Field F] {φ : Fin 3 → F} (hφ : φ ≠ 0) (c : F) :
    ∃ u : Fin 3 → F, φ ⬝ᵥ u = c := by
  obtain ⟨i, hi⟩ : ∃ i, φ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (funext h)
  refine ⟨Pi.single i (c / φ i), ?_⟩
  rw [dotProduct_single]
  field_simp

theorem aux_lineA {F : Type} [Field F] [CharP F 2] {a : (Fin 3 → F) ≃+ (Fin 3 → F)}
    {v φ v' φ' : Fin 3 → F} (hφ : φ ≠ 0) (hv' : v' ≠ 0)
    (hconj : ∀ u, a (u + (φ ⬝ᵥ u) • v) = a u + (φ' ⬝ᵥ a u) • v') :
    (∀ c : F, ∃ c' : F, a (c • v) = c' • v') ∧ (∀ u, φ ⬝ᵥ u = 0 → φ' ⬝ᵥ a u = 0) := by
  have key : ∀ u, a ((φ ⬝ᵥ u) • v) = (φ' ⬝ᵥ a u) • v' := by
    intro u
    have h := hconj u
    rw [map_add] at h
    exact add_left_cancel h
  refine ⟨fun c => ?_, fun u hu => ?_⟩
  · obtain ⟨u, hu⟩ := exists_dot_eq hφ c
    refine ⟨φ' ⬝ᵥ a u, ?_⟩
    rw [← hu]
    exact key u
  · have h := key u
    rw [hu, zero_smul, map_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_right hv'

theorem pair_indep {F : Type} [Field F] {v v' : Fin 3 → F} (hv : v ≠ 0)
    (H1 : ∀ c : F, v' ≠ c • v) {α β : F} (h : α • v + β • v' = 0) : α = 0 ∧ β = 0 := by
  by_cases hβ : β = 0
  · subst hβ
    rw [zero_smul, add_zero, smul_eq_zero] at h
    exact ⟨h.resolve_right hv, rfl⟩
  · exfalso
    apply H1 (-(α / β))
    have h2 : β • v' = -(α • v) := eq_neg_of_add_eq_zero_right h
    calc v' = β⁻¹ • (β • v') := (inv_smul_smul₀ hβ v').symm
      _ = β⁻¹ • (-(α • v)) := by rw [h2]
      _ = -(α / β) • v := by rw [smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

theorem line_image_of_conj {F : Type} [Field F] [CharP F 2] {a : (Fin 3 → F) ≃+ (Fin 3 → F)}
    (ha : ∀ u, a (a u) = u) {v φ v' φ' : Fin 3 → F} (hv : v ≠ 0) (hφ : φ ≠ 0) (hv' : v' ≠ 0)
    (hφ' : φ' ≠ 0) (hφv : φ ⬝ᵥ v = 0) (hφv' : φ' ⬝ᵥ v' = 0)
    (hconj : ∀ u, a (u + (φ ⬝ᵥ u) • v) = a u + (φ' ⬝ᵥ a u) • v') :
    (∀ c : F, ∃ c' : F, a (c • v) = c' • v') ∧ (∀ c : F, ∃ c' : F, a (c • v') = c' • v) ∧
      (∀ u, φ ⬝ᵥ u = 0 → φ' ⬝ᵥ a u = 0) ∧ (∀ u, φ' ⬝ᵥ u = 0 → φ ⬝ᵥ a u = 0) := by
  have hconj' : ∀ u, a (u + (φ' ⬝ᵥ u) • v') = a u + (φ ⬝ᵥ a u) • v := by
    intro u
    have h := hconj (a u)
    rw [ha] at h
    have h2 := congrArg (⇑a) h
    rw [ha] at h2
    exact h2.symm
  obtain ⟨c1, c3⟩ := aux_lineA hφ hv' hconj
  obtain ⟨c2, c4⟩ := aux_lineA hφ' hv hconj'
  exact ⟨c1, c2, c3, c4⟩

theorem ncard_range_commutator_le {F : Type} [Field F] [Fintype F] [CharP F 2]
    {a s : (Fin 3 → F) ≃+ (Fin 3 → F)} (ha : ∀ u, a (a u) = u) :
    (Set.range fun u => a (s (a (s.symm u))) - u).ncard ≤
      (Set.range fun u => a u - u).ncard * (Set.range fun u => a u - u).ncard := by
  have hsub : (Set.range fun u => a (s (a (s.symm u))) - u) ⊆
      (fun p : (Fin 3 → F) × (Fin 3 → F) => p.1 + a (s p.2)) ''
        ((Set.range fun u => a u - u) ×ˢ (Set.range fun u => a u - u)) := by
    rintro _ ⟨u, rfl⟩
    refine ⟨(a u - u, a (s.symm u) - s.symm u),
      Set.mk_mem_prod ⟨u, rfl⟩ ⟨s.symm u, rfl⟩, ?_⟩
    simp only [map_sub, s.apply_symm_apply]
    abel
  calc (Set.range fun u => a (s (a (s.symm u))) - u).ncard
      ≤ ((fun p : (Fin 3 → F) × (Fin 3 → F) => p.1 + a (s p.2)) ''
          ((Set.range fun u => a u - u) ×ˢ (Set.range fun u => a u - u))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ((Set.range fun u => a u - u) ×ˢ (Set.range fun u => a u - u)).ncard :=
        Set.ncard_image_le (Set.toFinite _)
    _ = (Set.range fun u => a u - u).ncard * (Set.range fun u => a u - u).ncard :=
        Set.ncard_prod

theorem parallel_of_ncard_le {F : Type} [Field F] [Fintype F] [CharP F 2] (hF : 8 ≤ Fintype.card F)
    {a : (Fin 3 → F) ≃+ (Fin 3 → F)} (ha : ∀ u, a (a u) = u)
    (hrank : (Set.range fun u => a u - u).ncard ≤ 4)
    {v φ v' φ' : Fin 3 → F} (hv : v ≠ 0) (hφ : φ ≠ 0) (hv' : v' ≠ 0) (hφ' : φ' ≠ 0)
    (hφv : φ ⬝ᵥ v = 0) (hφv' : φ' ⬝ᵥ v' = 0)
    (hconj : ∀ u, a (u + (φ ⬝ᵥ u) • v) = a u + (φ' ⬝ᵥ a u) • v') :
    (∃ c : F, v' = c • v) ∨ (∃ c : F, φ' = c • φ) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨H1, H2⟩ := hcon
  have hdouble : ∀ x : F, x + x = 0 := by
    intro x
    have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    calc x + x = 2 * x := by ring
      _ = 0 := by rw [h2, zero_mul]
  have hinv : ∀ u : Fin 3 → F,
      (u + (φ ⬝ᵥ u) • v) + (φ ⬝ᵥ (u + (φ ⬝ᵥ u) • v)) • v = u := by
    intro u
    rw [dotProduct_add, dotProduct_smul, hφv, smul_zero, add_zero, add_assoc, ← add_smul,
      hdouble (φ ⬝ᵥ u), zero_smul, add_zero]
  have hadd : ∀ x y : Fin 3 → F,
      (x + y) + (φ ⬝ᵥ (x + y)) • v = (x + (φ ⬝ᵥ x) • v) + (y + (φ ⬝ᵥ y) • v) := by
    intro x y
    rw [dotProduct_add, add_smul]
    abel
  obtain ⟨t, ht, hts⟩ : ∃ t : (Fin 3 → F) ≃+ (Fin 3 → F),
      (∀ u, t u = u + (φ ⬝ᵥ u) • v) ∧ (∀ u, t.symm u = u + (φ ⬝ᵥ u) • v) :=
    ⟨{ toFun := fun u => u + (φ ⬝ᵥ u) • v
       invFun := fun u => u + (φ ⬝ᵥ u) • v
       left_inv := fun u => hinv u
       right_inv := fun u => hinv u
       map_add' := fun x y => hadd x y }, fun u => rfl, fun u => rfl⟩
  have hconj' : ∀ u, a (t u) = a u + (φ' ⬝ᵥ a u) • v' := by
    intro u
    rw [ht u]
    exact hconj u
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fin 3 → F, ψ = φ' + (φ' ⬝ᵥ v) • φ := ⟨_, rfl⟩
  have hψu : ∀ u, ψ ⬝ᵥ u = φ' ⬝ᵥ u + (φ' ⬝ᵥ v) * (φ ⬝ᵥ u) := by
    intro u
    rw [hψ, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have hkey : ∀ u : Fin 3 → F,
      a (t (a (t.symm u))) - u = (φ ⬝ᵥ u) • v + (ψ ⬝ᵥ u) • v' := by
    intro u
    have h1 : a (t (a (t.symm u))) = t.symm u + (φ' ⬝ᵥ t.symm u) • v' := by
      rw [hconj', ha]
    rw [h1, hts u, dotProduct_add, dotProduct_smul, smul_eq_mul, hψu]
    module
  have hψnot : ∀ c : F, ψ ≠ c • φ := by
    intro c hc
    apply H2 (c - φ' ⬝ᵥ v)
    calc φ' = ψ - (φ' ⬝ᵥ v) • φ := by rw [hψ]; abel
      _ = c • φ - (φ' ⬝ᵥ v) • φ := by rw [hc]
      _ = (c - φ' ⬝ᵥ v) • φ := (sub_smul c (φ' ⬝ᵥ v) φ).symm
  obtain ⟨i, hi⟩ : ∃ i, φ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (funext h)
  obtain ⟨j, hj⟩ : ∃ j, φ i * ψ j - φ j * ψ i ≠ 0 := by
    by_contra h
    push Not at h
    apply hψnot (ψ i / φ i)
    funext k
    have hk := h k
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hi]
    linear_combination hk
  obtain ⟨D, hD⟩ : ∃ D : F, D = φ i * ψ j - φ j * ψ i := ⟨_, rfl⟩
  have hDne : D ≠ 0 := by
    rw [hD]
    exact hj
  have hsurj : ∀ α β : F, ∃ u : Fin 3 → F, φ ⬝ᵥ u = α ∧ ψ ⬝ᵥ u = β := by
    intro α β
    refine ⟨Pi.single i ((α * ψ j - φ j * β) / D) + Pi.single j ((φ i * β - ψ i * α) / D),
      ?_, ?_⟩
    · rw [dotProduct_add, dotProduct_single, dotProduct_single, mul_div_assoc', mul_div_assoc',
        ← add_div, div_eq_iff hDne, hD]
      ring
    · rw [dotProduct_add, dotProduct_single, dotProduct_single, mul_div_assoc', mul_div_assoc',
        ← add_div, div_eq_iff hDne, hD]
      ring
  have hsub : Set.range (fun p : F × F => p.1 • v + p.2 • v') ⊆
      Set.range fun u => a (t (a (t.symm u))) - u := by
    rintro _ ⟨⟨α, β⟩, rfl⟩
    obtain ⟨u, hu1, hu2⟩ := hsurj α β
    refine ⟨u, ?_⟩
    show a (t (a (t.symm u))) - u = α • v + β • v'
    rw [hkey u, hu1, hu2]
  have hinjg : Function.Injective (fun p : F × F => p.1 • v + p.2 • v') := by
    rintro ⟨α, β⟩ ⟨α', β'⟩ h
    dsimp only at h
    have h0 : (α - α') • v + (β - β') • v' = 0 := by
      calc (α - α') • v + (β - β') • v' = (α • v + β • v') - (α' • v + β' • v') := by module
        _ = 0 := by rw [h, sub_self]
    obtain ⟨h1, h1'⟩ := pair_indep hv H1 h0
    exact Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h1')
  have hg : (Set.range (fun p : F × F => p.1 • v + p.2 • v')).ncard =
      Fintype.card F * Fintype.card F := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinjg, Set.ncard_univ, Nat.card_prod,
      Nat.card_eq_fintype_card]
  have hcard1 : Fintype.card F * Fintype.card F ≤
      (Set.range fun u => a (t (a (t.symm u))) - u).ncard := by
    rw [← hg]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hle2 := ncard_range_commutator_le (a := a) (s := t) ha
  have hle3 : (Set.range fun u => a u - u).ncard * (Set.range fun u => a u - u).ncard ≤ 4 * 4 :=
    Nat.mul_le_mul hrank hrank
  have hle4 : 8 * 8 ≤ Fintype.card F * Fintype.card F := Nat.mul_le_mul hF hF
  have hfin := le_trans hle4 (le_trans hcard1 (le_trans hle2 hle3))
  norm_num at hfin

end CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatA

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatI

def tvM {F : Type} [Field F] (φ v : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  1 + Matrix.vecMulVec v φ

theorem tvM_mulVec {F : Type} [Field F] (φ v u : Fin 3 → F) :
    tvM φ v *ᵥ u = u + (φ ⬝ᵥ u) • v := by
  unfold tvM
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul, Fin.sum_univ_three]
  ring

theorem det_tvM {F : Type} [Field F] {φ v : Fin 3 → F} (h : φ ⬝ᵥ v = 0) :
    (tvM φ v).det = 1 := by
  unfold tvM
  rw [Matrix.vecMulVec_eq (Fin 1), Matrix.det_one_add_replicateCol_mul_replicateRow, h, add_zero]

theorem tvM_ne_one {F : Type} [Field F] {φ v : Fin 3 → F} (hφ : φ ≠ 0) (hv : v ≠ 0) :
    tvM φ v ≠ 1 := by
  intro h
  have key : ∀ u : Fin 3 → F, (φ ⬝ᵥ u) • v = 0 := by
    intro u
    have h1 := tvM_mulVec φ v u
    rw [h, Matrix.one_mulVec] at h1
    calc (φ ⬝ᵥ u) • v = (u + (φ ⬝ᵥ u) • v) - u := by abel
      _ = u - u := by rw [← h1]
      _ = 0 := sub_self u
  obtain ⟨j, hj⟩ : ∃ j, φ j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ (funext hcon)
  have h2 := key (Pi.single j 1)
  rw [dotProduct_single, mul_one] at h2
  exact hv ((smul_eq_zero.1 h2).resolve_left hj)

theorem sq_eq_one_of_conj {F : Type} [Field F] {a : (Fin 3 → F) ≃+ (Fin 3 → F)}
    (ha : ∀ u, a (a u) = u) {M M' : Matrix (Fin 3) (Fin 3) F} (hM : M * M = 1)
    (h : ∀ u, a (M *ᵥ u) = M' *ᵥ a u) : M' * M' = 1 := by
  apply Matrix.ext_iff_mulVec.2
  intro w
  have hw1 : M' *ᵥ w = a (M *ᵥ a w) := by
    have h1 := h (a w)
    rw [ha] at h1
    exact h1.symm
  rw [Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hw1, ← h (M *ᵥ a w), Matrix.mulVec_mulVec, hM,
    Matrix.one_mulVec, ha]

theorem ne_one_of_conj {F : Type} [Field F] {a : (Fin 3 → F) ≃+ (Fin 3 → F)}
    (ha : ∀ u, a (a u) = u) {M M' : Matrix (Fin 3) (Fin 3) F} (hM1 : M ≠ 1)
    (h : ∀ u, a (M *ᵥ u) = M' *ᵥ a u) : M' ≠ 1 := by
  intro hM'
  apply hM1
  apply Matrix.ext_iff_mulVec.2
  intro u
  have h1 : a (M *ᵥ u) = a u := by
    rw [h u, hM', Matrix.one_mulVec]
  rw [Matrix.one_mulVec]
  exact a.injective h1

theorem rankOne_of_sq_eq_zero {F : Type} [Field F] {n : Matrix (Fin 3) (Fin 3) F}
    (hnn : n * n = 0) (hn0 : n ≠ 0) :
    ∃ v φ : Fin 3 → F, v ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ v = 0 ∧ ∀ u, n *ᵥ u = (φ ⬝ᵥ u) • v := by
  obtain ⟨u0, hu0⟩ : ∃ u0 : Fin 3 → F, n *ᵥ u0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hn0 (Matrix.ext_iff_mulVec.2 fun u => by rw [Matrix.zero_mulVec]; exact hcon u)
  have hle : LinearMap.range (Matrix.mulVecLin n) ≤ LinearMap.ker (Matrix.mulVecLin n) := by
    rintro x ⟨u, rfl⟩
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hnn,
      Matrix.zero_mulVec]
  have hsum : Module.finrank F (LinearMap.range (Matrix.mulVecLin n)) +
      Module.finrank F (LinearMap.ker (Matrix.mulVecLin n)) = 3 := by
    rw [LinearMap.finrank_range_add_finrank_ker, Module.finrank_fin_fun]
  have hmono : Module.finrank F (LinearMap.range (Matrix.mulVecLin n)) ≤
      Module.finrank F (LinearMap.ker (Matrix.mulVecLin n)) :=
    Submodule.finrank_mono hle
  have hw0 : (⟨n *ᵥ u0, LinearMap.mem_range.2 ⟨u0, rfl⟩⟩ :
      LinearMap.range (Matrix.mulVecLin n)) ≠ 0 := by
    intro h
    apply hu0
    simpa using congrArg Subtype.val h
  have hpos : 0 < Module.finrank F (LinearMap.range (Matrix.mulVecLin n)) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨_, hw0⟩
  have hone : Module.finrank F (LinearMap.range (Matrix.mulVecLin n)) = 1 := by omega
  have hall := (finrank_eq_one_iff_of_nonzero' _ hw0).1 hone
  have hcoef : ∀ u : Fin 3 → F, ∃ c : F, n *ᵥ u = c • (n *ᵥ u0) := by
    intro u
    obtain ⟨c, hc⟩ := hall ⟨n *ᵥ u, LinearMap.mem_range.2 ⟨u, rfl⟩⟩
    refine ⟨c, ?_⟩
    have h2 : c • (n *ᵥ u0) = n *ᵥ u := by
      simpa using congrArg Subtype.val hc
    exact h2.symm
  obtain ⟨v, hv, hcv⟩ : ∃ v : Fin 3 → F, v ≠ 0 ∧ ∀ u : Fin 3 → F, ∃ c : F, n *ᵥ u = c • v :=
    ⟨n *ᵥ u0, hu0, hcoef⟩
  choose c hc using hcv
  obtain ⟨φ, hφdef⟩ : ∃ φ : Fin 3 → F, ∀ j, φ j = c (Pi.single j 1) :=
    ⟨fun j => c (Pi.single j 1), fun j => rfl⟩
  have hentry : ∀ i j, n i j = φ j * v i := by
    intro i j
    have h1 := congrFun (hc (Pi.single j 1)) i
    rw [hφdef j]
    simpa [Matrix.mulVec_single_one] using h1
  have hmul : ∀ u : Fin 3 → F, n *ᵥ u = (φ ⬝ᵥ u) • v := by
    intro u
    funext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hentry, Pi.smul_apply, smul_eq_mul]
    ring
  have hφ0 : φ ≠ 0 := by
    intro h0
    apply hu0
    rw [hmul u0, h0, zero_dotProduct, zero_smul]
  have hφv : φ ⬝ᵥ v = 0 := by
    obtain ⟨j, hj⟩ : ∃ j, φ j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hφ0 (funext hcon)
    have hu : φ ⬝ᵥ Pi.single j (φ j)⁻¹ = 1 := by
      rw [dotProduct_single, mul_inv_cancel₀ hj]
    have h2 : n *ᵥ v = (φ ⬝ᵥ v) • v := hmul v
    have h3 : n *ᵥ (n *ᵥ Pi.single j (φ j)⁻¹) = n *ᵥ v := by
      rw [hmul (Pi.single j (φ j)⁻¹), Matrix.mulVec_smul, hu, one_smul]
    have h4 : (φ ⬝ᵥ v) • v = 0 := by
      rw [← h2, ← h3, Matrix.mulVec_mulVec, hnn, Matrix.zero_mulVec]
    exact (smul_eq_zero.1 h4).resolve_right hv
  exact ⟨v, φ, hv, hφ0, hφv, hmul⟩

theorem exists_transvection_of_sq_eq_one {F : Type} [Field F] [CharP F 2]
    {y : Matrix (Fin 3) (Fin 3) F} (hy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ v φ : Fin 3 → F, v ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ v = 0 ∧ ∀ u, y *ᵥ u = u + (φ ⬝ᵥ u) • v := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hdouble : ∀ A : Matrix (Fin 3) (Fin 3) F, A + A = 0 := by
    intro A
    have hA : A + A = (2 : F) • A := by rw [two_smul]
    rw [hA, h2, zero_smul]
  have hnn : (y - 1) * (y - 1) = 0 := by
    have e1 : (1 : Matrix (Fin 3) (Fin 3) F) + 1 = 0 := hdouble 1
    have e2 : (y - 1) * (y - 1) = y * y - y - y + 1 := by noncomm_ring
    rw [e2, hy]
    calc (1 : Matrix (Fin 3) (Fin 3) F) - y - y + 1 = (1 + 1) - (y + y) := by abel
      _ = 0 := by rw [e1, hdouble y, sub_zero]
  have hn0 : y - 1 ≠ 0 := fun h => hy1 (sub_eq_zero.1 h)
  obtain ⟨v, φ, hv, hφ, hφv, hmul⟩ := rankOne_of_sq_eq_zero hnn hn0
  have hy' : (1 : Matrix (Fin 3) (Fin 3) F) + (y - 1) = y := by abel
  refine ⟨v, φ, hv, hφ, hφv, fun u => ?_⟩
  calc y *ᵥ u = ((1 : Matrix (Fin 3) (Fin 3) F) + (y - 1)) *ᵥ u := by rw [hy']
    _ = u + (y - 1) *ᵥ u := by rw [Matrix.add_mulVec, Matrix.one_mulVec]
    _ = u + (φ ⬝ᵥ u) • v := by rw [hmul u]

end CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatI

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatR

theorem ncard_range_le_of_offender {U : Type} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (A : Subgroup (U ≃ₗ[ZMod 2] U)) {a : U ≃ₗ[ZMod 2] U} (ha : a ∈ A)
    (hoff : Nat.card U ≤ Nat.card ↥A * Nat.card {u : U // ∀ a ∈ A, a u = u}) :
    (Set.range fun u => a u - u).ncard ≤ Nat.card ↥A := by
  obtain ⟨d, hd⟩ : ∃ d : U →+ U, ∀ u, d u = a u - u :=
    ⟨AddMonoidHom.mk' (fun u => a u - u) (fun x y => by simp only [map_add]; abel),
      fun u => rfl⟩
  have hset : Set.range (fun u => a u - u) = (d.range : Set U) := by
    ext x
    simp [hd, AddMonoidHom.mem_range]
  have hU : Nat.card U = Nat.card ↥d.ker * Nat.card ↥d.range := by
    rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]
  have hmem : ∀ u : {u : U // ∀ b ∈ A, b u = u}, u.1 ∈ d.ker := by
    intro u
    rw [AddMonoidHom.mem_ker, hd, u.2 a ha, sub_self]
  have hC : Nat.card {u : U // ∀ b ∈ A, b u = u} ≤ Nat.card ↥d.ker := by
    refine Nat.card_le_card_of_injective (fun u => (⟨u.1, hmem u⟩ : d.ker)) ?_
    intro x y hxy
    have h := congrArg Subtype.val hxy
    exact Subtype.ext h
  have hpos : 0 < Nat.card ↥d.ker := Nat.card_pos
  have h1 : Nat.card ↥d.range * Nat.card ↥d.ker ≤ Nat.card ↥A * Nat.card ↥d.ker := by
    calc Nat.card ↥d.range * Nat.card ↥d.ker = Nat.card U := by
          rw [hU]; exact Nat.mul_comm _ _
      _ ≤ Nat.card ↥A * Nat.card {u : U // ∀ b ∈ A, b u = u} := hoff
      _ ≤ Nat.card ↥A * Nat.card ↥d.ker := Nat.mul_le_mul le_rfl hC
  rw [← Nat.card_coe_set_eq, hset, SetLike.coe_sort_coe]
  exact Nat.le_of_mul_le_mul_right h1 hpos

end CFSG.RankThree.PartTwo.Sec15.F153L3K.Out.NatR
