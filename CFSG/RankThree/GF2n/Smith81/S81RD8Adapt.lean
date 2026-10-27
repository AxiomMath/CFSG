module

public import CFSG.RankThree.GF2n.Smith81.S81RDot
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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

open Matrix

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type} [Field K]

private theorem adapted_helper {p q r a : Fin 6 → K} {x y z : K}
    (hind : ∀ x' y' z' : K, x' • p + y' • q + z' • r = 0 → x' = 0 ∧ y' = 0 ∧ z' = 0)
    (ha_eq : a = x • p + y • q + z • r) (hx : x ≠ 0) :
    LinearIndependent K ![a, q, r] ∧ p ∈ Submodule.span K (Set.range ![a, q, r]) ∧
      q ∈ Submodule.span K (Set.range ![a, q, r]) ∧
      r ∈ Submodule.span K (Set.range ![a, q, r]) := by
  have hlin : LinearIndependent K ![a, q, r] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    have hg' : g 0 • a + g 1 • q + g 2 • r = 0 := by simpa using hg
    rw [ha_eq] at hg'
    obtain ⟨h1, h2, h3⟩ := hind (g 0 * x) (g 0 * y + g 1) (g 0 * z + g 2)
      (by linear_combination (norm := module) hg')
    have hg0 : g 0 = 0 := (mul_eq_zero.mp h1).resolve_right hx
    have hg1 : g 1 = 0 := by simpa [hg0] using h2
    have hg2 : g 2 = 0 := by simpa [hg0] using h3
    intro i
    fin_cases i
    exacts [hg0, hg1, hg2]
  have ha_mem : a ∈ Submodule.span K (Set.range ![a, q, r]) :=
    Submodule.subset_span ⟨0, by simp⟩
  have hq_mem : q ∈ Submodule.span K (Set.range ![a, q, r]) :=
    Submodule.subset_span ⟨1, by simp⟩
  have hr_mem : r ∈ Submodule.span K (Set.range ![a, q, r]) :=
    Submodule.subset_span ⟨2, by simp⟩
  have hp : p = x⁻¹ • (a - y • q - z • r) := by
    rw [ha_eq, show x • p + y • q + z • r - y • q - z • r = x • p by abel, inv_smul_smul₀ hx]
  refine ⟨hlin, ?_, hq_mem, hr_mem⟩
  rw [hp]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _
    (Submodule.sub_mem _ ha_mem (Submodule.smul_mem _ _ hq_mem)) (Submodule.smul_mem _ _ hr_mem))

theorem exists_pair_in_kernels {a f g : Fin 6 → K} (ha : a ≠ 0) :
    ∃ u v : Fin 6 → K, LinearIndependent K ![a, u, v] ∧
      f ⬝ᵥ u = 0 ∧ f ⬝ᵥ v = 0 ∧ g ⬝ᵥ u = 0 ∧ g ⬝ᵥ v = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  have hj' : a j ≠ 0 := hj
  obtain ⟨θ, hθa⟩ : ∃ θ : Fin 6 → K, θ ⬝ᵥ a = 1 :=
    ⟨Pi.single j (a j)⁻¹, by rw [single_dotProduct, inv_mul_cancel₀ hj']⟩
  obtain ⟨u, hu0, hu⟩ := exists_ne_zero_dot_eq_zero (n := 6) (m := 3) (by norm_num) ![f, g, θ]
  have hf_u : f ⬝ᵥ u = 0 := hu 0
  have hg_u : g ⬝ᵥ u = 0 := hu 1
  have hθ_u : θ ⬝ᵥ u = 0 := hu 2
  have hu_ne : ∀ c : K, u ≠ c • a := by
    intro c hc
    have hc0 : c = 0 := by
      have h1 : θ ⬝ᵥ u = c := by
        rw [hc, dotProduct_smul, hθa, smul_eq_mul, mul_one]
      rw [hθ_u] at h1
      exact h1.symm
    apply hu0
    rw [hc, hc0, zero_smul]
  obtain ⟨θ', -, hθ'u⟩ := exists_dot_eq_zero_dot_ne ha hu_ne
  obtain ⟨v, hv0, hv⟩ :=
    exists_ne_zero_dot_eq_zero (n := 6) (m := 4) (by norm_num) ![f, g, θ, θ']
  have hf_v : f ⬝ᵥ v = 0 := hv 0
  have hg_v : g ⬝ᵥ v = 0 := hv 1
  have hθ_v : θ ⬝ᵥ v = 0 := hv 2
  have hθ'_v : θ' ⬝ᵥ v = 0 := hv 3
  refine ⟨u, v, ?_, hf_u, hf_v, hg_u, hg_v⟩
  rw [Fintype.linearIndependent_iff]
  intro c hsum
  rw [Fin.sum_univ_three] at hsum
  have hsum' : c 0 • a + c 1 • u + c 2 • v = 0 := by simpa using hsum
  have e0 : c 0 = 0 := by
    have h := congrArg (fun x => θ ⬝ᵥ x) hsum'
    simpa [dotProduct_add, dotProduct_smul, hθa, hθ_u, hθ_v] using h
  have e1 : c 1 = 0 := by
    have hsum2 : c 1 • u + c 2 • v = 0 := by simpa [e0] using hsum'
    have h := congrArg (fun x => θ' ⬝ᵥ x) hsum2
    have h' : c 1 * (θ' ⬝ᵥ u) = 0 := by
      simpa [dotProduct_add, dotProduct_smul, hθ'_v] using h
    exact (mul_eq_zero.mp h').resolve_right hθ'u
  have e2 : c 2 = 0 := by
    have hsum2 : c 2 • v = 0 := by simpa [e0, e1] using hsum'
    exact (smul_eq_zero.mp hsum2).resolve_right hv0
  intro i
  fin_cases i
  exacts [e0, e1, e2]

theorem exists_adapted_triple {s : Fin 3 → Fin 6 → K} (hs : LinearIndependent K s) {a : Fin 6 → K}
    (has : a ∈ Submodule.span K (Set.range s)) (ha : a ≠ 0) :
    ∃ u₁ v₁ : Fin 6 → K, LinearIndependent K ![a, u₁, v₁] ∧
      u₁ ∈ Submodule.span K (Set.range s) ∧ v₁ ∈ Submodule.span K (Set.range s) ∧
      ∀ i, s i ∈ Submodule.span K (Set.range ![a, u₁, v₁]) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp has
  rw [Fin.sum_univ_three] at hc
  have hind : ∀ x y z : K, x • s 0 + y • s 1 + z • s 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
    intro x y z h
    have key := Fintype.linearIndependent_iff.mp hs ![x, y, z]
      (by simpa [Fin.sum_univ_three] using h)
    exact ⟨key 0, key 1, key 2⟩
  rcases eq_or_ne (c 0) 0 with h0 | h0
  · rcases eq_or_ne (c 1) 0 with h1 | h1
    · rcases eq_or_ne (c 2) 0 with h2 | h2
      · exfalso
        apply ha
        rw [← hc]
        simp [h0, h1, h2]
      ·
        have hind' : ∀ x y z : K, x • s 2 + y • s 0 + z • s 1 = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
          intro x y z h
          obtain ⟨k1, k2, k3⟩ := hind y z x (by rw [← h]; abel)
          exact ⟨k3, k1, k2⟩
        obtain ⟨hli, hp, hq, hr⟩ := adapted_helper (a := a) (p := s 2) (q := s 0) (r := s 1)
          (x := c 2) (y := c 0) (z := c 1) hind' (by rw [← hc]; abel) h2
        refine ⟨s 0, s 1, hli, Submodule.subset_span ⟨0, rfl⟩, Submodule.subset_span ⟨1, rfl⟩, ?_⟩
        intro i
        fin_cases i
        exacts [hq, hr, hp]
    ·
      have hind' : ∀ x y z : K, x • s 1 + y • s 0 + z • s 2 = 0 → x = 0 ∧ y = 0 ∧ z = 0 := by
        intro x y z h
        obtain ⟨k1, k2, k3⟩ := hind y x z (by rw [← h]; abel)
        exact ⟨k2, k1, k3⟩
      obtain ⟨hli, hp, hq, hr⟩ := adapted_helper (a := a) (p := s 1) (q := s 0) (r := s 2)
        (x := c 1) (y := c 0) (z := c 2) hind' (by rw [← hc]; abel) h1
      refine ⟨s 0, s 2, hli, Submodule.subset_span ⟨0, rfl⟩, Submodule.subset_span ⟨2, rfl⟩, ?_⟩
      intro i
      fin_cases i
      exacts [hq, hp, hr]
  ·
    obtain ⟨hli, hp, hq, hr⟩ := adapted_helper (a := a) (p := s 0) (q := s 1) (r := s 2)
      (x := c 0) (y := c 1) (z := c 2) hind hc.symm h0
    refine ⟨s 1, s 2, hli, Submodule.subset_span ⟨1, rfl⟩, Submodule.subset_span ⟨2, rfl⟩, ?_⟩
    intro i
    fin_cases i
    exacts [hp, hq, hr]

end CFSG.RankThree.GF2n.Smith81.A5Cube
