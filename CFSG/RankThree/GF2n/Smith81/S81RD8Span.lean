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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Sheaves.Init

open Matrix

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

variable {K : Type} [Field K]

theorem exists_dot_ker_not_mem_span {f : Fin 6 → K} (hf : f ≠ 0) (s : Fin 3 → Fin 6 → K) :
    ∃ w : Fin 6 → K, f ⬝ᵥ w = 0 ∧ w ∉ Submodule.span K (Set.range s) := by
  by_contra hcon
  have hcon' : ∀ w, f ⬝ᵥ w = 0 → w ∈ Submodule.span K (Set.range s) := fun w h1 => by
    by_contra h2
    exact hcon ⟨w, h1, h2⟩
  obtain ⟨F, hF⟩ : ∃ F : (Fin 6 → K) →ₗ[K] K, ∀ w, F w = f ⬝ᵥ w :=
    ⟨{ toFun := fun w => f ⬝ᵥ w
       map_add' := fun x y => by simp [dotProduct_add]
       map_smul' := fun c x => by simp }, fun w => rfl⟩
  have hsurj : LinearMap.range F = ⊤ := by
    rw [LinearMap.range_eq_top]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hf
    have hj' : f j ≠ 0 := by simpa using hj
    intro c
    refine ⟨Pi.single j (c / f j), ?_⟩
    rw [hF, dotProduct_single]
    field_simp
  have hker : Module.finrank K (LinearMap.ker F) = 5 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker F
    rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h1
    omega
  have hle : LinearMap.ker F ≤ Submodule.span K (Set.range s) := by
    intro w hw
    apply hcon' w
    rw [← hF]
    exact LinearMap.mem_ker.mp hw
  have h3 : Module.finrank K (Submodule.span K (Set.range s)) ≤ 3 := by
    have h := finrank_range_le_card (R := K) s
    rw [Fintype.card_fin] at h
    exact h
  have h4 := Submodule.finrank_mono hle
  omega

theorem not_linearIndependent_of_collinear {a : Fin 6 → K} {s : Fin 3 → Fin 6 → K}
    (h : ∀ i, ∃ c : K, s i = c • a) : ¬ LinearIndependent K s := by
  choose c hc using h
  intro hli
  obtain ⟨x, hx0, hxc⟩ := exists_ne_zero_dot_eq_zero (m := 1) (n := 3) (by norm_num) (fun _ => c)
  have hxc' : x ⬝ᵥ c = 0 := by
    rw [dotProduct_comm]
    exact hxc 0
  have h1 : ∑ i, x i • s i = (x ⬝ᵥ c) • a := by
    simp only [dotProduct, hc, smul_smul, Finset.sum_smul]
  have hsum : ∑ i, x i • s i = 0 := by
    rw [h1, hxc', zero_smul]
  exact hx0 (funext fun i => Fintype.linearIndependent_iff.mp hli x hsum i)

theorem dot_eq_zero_of_mem_span {n : ℕ} {f : Fin n → K} {ι : Type*} {s : ι → Fin n → K}
    (hs : ∀ i, f ⬝ᵥ s i = 0) {v : Fin n → K} (hv : v ∈ Submodule.span K (Set.range s)) :
    f ⬝ᵥ v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hs i
  | zero => simp
  | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
  | smul c x _ hx => rw [dotProduct_smul, hx, smul_zero]

theorem mulVec_mem_span_of_images {G : Matrix (Fin 6) (Fin 6) K} {a u₁ v₁ u v z : Fin 6 → K}
    (hz : z ∈ Submodule.span K (Set.range ![a, u₁, v₁])) (ha : G.mulVec a = a)
    (hu : G.mulVec u₁ = u) (hv : G.mulVec v₁ = v) :
    G.mulVec z ∈ Submodule.span K (Set.range ![a, u, v]) := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (R := K)).mp hz
  refine (Submodule.mem_span_range_iff_exists_fun (R := K)).mpr ⟨c, ?_⟩
  simp [Fin.sum_univ_three, Matrix.mulVec_add, Matrix.mulVec_smul, ha, hu, hv]

end CFSG.RankThree.GF2n.Smith81.A5Cube
