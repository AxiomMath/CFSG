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

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem commutator_xg_comm {G : Type*} [Group G] (x g a c d : G) (m κ : ℤ)
    (hxa : x * a * x⁻¹ = d ^ m * a) (hxc : x * c = c * x) (hxd : x * d = d * x)
    (hga : g * a = a * g) (hgc : g * c * g⁻¹ = d ^ κ * c) (hgd : g * d = d * g)
    (hac : a * c = c * a) (had : a * d = d * a) (hcd : c * d = d * c) :
    ∀ u ∈ Subgroup.closure ({c, a, d} : Set G),
      (x * g * x⁻¹ * g⁻¹) * u = u * (x * g * x⁻¹ * g⁻¹) := by
  have hxd' : Commute x d := hxd
  have hgd' : Commute g d := hgd
  have hxc' : Commute x c := hxc
  have hga' : Commute g a := hga
  have hxDm : Commute x (d ^ m) := hxd'.zpow_right m
  have hgDm : Commute g (d ^ m) := hgd'.zpow_right m
  have hxDk : Commute x (d ^ κ) := hxd'.zpow_right κ
  have hgDk : Commute g (d ^ κ) := hgd'.zpow_right κ
  have hG1 : g⁻¹ * a = a * g⁻¹ := hga'.inv_left.eq
  have hA1 : d ^ m * (x⁻¹ * a) = a * x⁻¹ := by
    calc d ^ m * (x⁻¹ * a) = (d ^ m * x⁻¹) * a := by simp only [mul_assoc]
      _ = (x⁻¹ * d ^ m) * a := by rw [hxDm.inv_left.eq.symm]
      _ = x⁻¹ * (d ^ m * a) := by simp only [mul_assoc]
      _ = x⁻¹ * (x * a * x⁻¹) := by rw [hxa]
      _ = a * x⁻¹ := by group
  have hA1' : x⁻¹ * a = (d ^ m)⁻¹ * (a * x⁻¹) := eq_inv_mul_of_mul_eq hA1
  have hxa2 : x * a = d ^ m * a * x := by
    rw [← hxa]; group
  have hgDm_inv : g * (d ^ m)⁻¹ = (d ^ m)⁻¹ * g := hgDm.inv_right.eq
  have hxDm_inv : x * (d ^ m)⁻¹ = (d ^ m)⁻¹ * x := hxDm.inv_right.eq
  have ha : x * g * x⁻¹ * g⁻¹ * a = a * (x * g * x⁻¹ * g⁻¹) := by
    calc x * g * x⁻¹ * g⁻¹ * a = x * g * x⁻¹ * (g⁻¹ * a) := by simp only [mul_assoc]
      _ = x * g * x⁻¹ * (a * g⁻¹) := by rw [hG1]
      _ = x * g * (x⁻¹ * a) * g⁻¹ := by simp only [mul_assoc]
      _ = x * g * ((d ^ m)⁻¹ * (a * x⁻¹)) * g⁻¹ := by rw [hA1']
      _ = x * (g * (d ^ m)⁻¹) * (a * x⁻¹) * g⁻¹ := by simp only [mul_assoc]
      _ = x * ((d ^ m)⁻¹ * g) * (a * x⁻¹) * g⁻¹ := by rw [hgDm_inv]
      _ = x * (d ^ m)⁻¹ * (g * a) * x⁻¹ * g⁻¹ := by simp only [mul_assoc]
      _ = x * (d ^ m)⁻¹ * (a * g) * x⁻¹ * g⁻¹ := by rw [hga]
      _ = (x * (d ^ m)⁻¹) * a * g * x⁻¹ * g⁻¹ := by simp only [mul_assoc]
      _ = ((d ^ m)⁻¹ * x) * a * g * x⁻¹ * g⁻¹ := by rw [hxDm_inv]
      _ = (d ^ m)⁻¹ * (x * a) * g * x⁻¹ * g⁻¹ := by simp only [mul_assoc]
      _ = (d ^ m)⁻¹ * (d ^ m * a * x) * g * x⁻¹ * g⁻¹ := by rw [hxa2]
      _ = a * (x * g * x⁻¹ * g⁻¹) := by group
  have hA : d ^ κ * (g⁻¹ * c) = c * g⁻¹ := by
    calc d ^ κ * (g⁻¹ * c) = (d ^ κ * g⁻¹) * c := by simp only [mul_assoc]
      _ = (g⁻¹ * d ^ κ) * c := by rw [hgDk.inv_left.eq.symm]
      _ = g⁻¹ * (d ^ κ * c) := by simp only [mul_assoc]
      _ = g⁻¹ * (g * c * g⁻¹) := by rw [hgc]
      _ = c * g⁻¹ := by group
  have hB : g⁻¹ * c = (d ^ κ)⁻¹ * (c * g⁻¹) := eq_inv_mul_of_mul_eq hA
  have hC_x : x⁻¹ * ((d ^ κ)⁻¹ * c) = (d ^ κ)⁻¹ * c * x⁻¹ :=
    (hxDk.inv_right.mul_right hxc').inv_left.eq
  have hgK_inv : g * (d ^ κ)⁻¹ = (d ^ κ)⁻¹ * g := hgDk.inv_right.eq
  have hgc' : g * c = d ^ κ * c * g := by
    rw [← hgc]; group
  have hc : x * g * x⁻¹ * g⁻¹ * c = c * (x * g * x⁻¹ * g⁻¹) := by
    calc x * g * x⁻¹ * g⁻¹ * c = x * g * x⁻¹ * (g⁻¹ * c) := by simp only [mul_assoc]
      _ = x * g * x⁻¹ * ((d ^ κ)⁻¹ * (c * g⁻¹)) := by rw [hB]
      _ = x * g * (x⁻¹ * ((d ^ κ)⁻¹ * c)) * g⁻¹ := by simp only [mul_assoc]
      _ = x * g * ((d ^ κ)⁻¹ * c * x⁻¹) * g⁻¹ := by rw [hC_x]
      _ = x * (g * (d ^ κ)⁻¹) * c * x⁻¹ * g⁻¹ := by simp only [mul_assoc]
      _ = x * ((d ^ κ)⁻¹ * g) * c * x⁻¹ * g⁻¹ := by rw [hgK_inv]
      _ = x * (d ^ κ)⁻¹ * (g * c) * x⁻¹ * g⁻¹ := by simp only [mul_assoc]
      _ = x * (d ^ κ)⁻¹ * (d ^ κ * c * g) * x⁻¹ * g⁻¹ := by rw [hgc']
      _ = (x * (d ^ κ)⁻¹ * d ^ κ) * c * g * x⁻¹ * g⁻¹ := by simp only [mul_assoc]
      _ = x * c * g * x⁻¹ * g⁻¹ := by group
      _ = c * x * g * x⁻¹ * g⁻¹ := by rw [hxc]
      _ = c * (x * g * x⁻¹ * g⁻¹) := by simp only [mul_assoc]
  have hdx : Commute d x := hxd'.symm
  have hdg : Commute d g := hgd'.symm
  have hd : x * g * x⁻¹ * g⁻¹ * d = d * (x * g * x⁻¹ * g⁻¹) :=
    (((hdx.mul_right hdg).mul_right hdx.inv_right).mul_right hdg.inv_right).eq.symm
  have hgen : ∀ t ∈ ({c, a, d} : Set G), x * g * x⁻¹ * g⁻¹ * t = t * (x * g * x⁻¹ * g⁻¹) := by
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with h | h | h
    · rw [h]; exact hc
    · rw [h]; exact ha
    · rw [h]; exact hd
  have hcent : Subgroup.closure ({c, a, d} : Set G) ≤
      Subgroup.centralizer ({x * g * x⁻¹ * g⁻¹} : Set G) := by
    rw [Subgroup.closure_le]
    intro t ht
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro q hq
    rw [Set.mem_singleton_iff.mp hq]
    exact hgen t ht
  intro u hu
  exact Subgroup.mem_centralizer_iff.mp (hcent hu) _ (Set.mem_singleton _)

theorem mem_closure_union_zpowers_form {G : Type*} [Group G] (A : Subgroup G) (y : G)
    (hAy : ∀ u ∈ A, u * y = y * u) {z : G} :
    z ∈ Subgroup.closure ((A : Set G) ∪ {y}) ↔ ∃ (i : ℤ) (u : G), u ∈ A ∧ z = y ^ i * u := by
  constructor
  · intro hz
    refine Subgroup.closure_induction
      (p := fun w _ => ∃ (i : ℤ) (u : G), u ∈ A ∧ w = y ^ i * u) ?_ ?_ ?_ ?_ hz
    · rintro w (hw | hw)
      · exact ⟨0, w, hw, by simp⟩
      · rw [Set.mem_singleton_iff] at hw
        exact ⟨1, 1, A.one_mem, by simp [hw]⟩
    · exact ⟨0, 1, A.one_mem, by simp⟩
    · rintro w₁ w₂ _ _ ⟨i, u, hu, rfl⟩ ⟨j, v, hv, rfl⟩
      have huy : Commute u y := hAy u hu
      have hcomm : u * y ^ j = y ^ j * u := (huy.zpow_right j).eq
      refine ⟨i + j, u * v, mul_mem hu hv, ?_⟩
      calc y ^ i * u * (y ^ j * v) = y ^ i * (u * y ^ j) * v := by simp only [mul_assoc]
        _ = y ^ i * (y ^ j * u) * v := by rw [hcomm]
        _ = y ^ (i + j) * (u * v) := by rw [zpow_add]; simp only [mul_assoc]
    · rintro w _ ⟨i, u, hu, rfl⟩
      refine ⟨-i, u⁻¹, inv_mem hu, ?_⟩
      have huy : Commute u y := hAy u hu
      have hcomm : u⁻¹ * y ^ (-i) = y ^ (-i) * u⁻¹ :=
        ((huy.inv_left).zpow_right (-i)).eq
      calc (y ^ i * u)⁻¹ = u⁻¹ * (y ^ i)⁻¹ := mul_inv_rev _ _
        _ = u⁻¹ * y ^ (-i) := by rw [zpow_neg]
        _ = y ^ (-i) * u⁻¹ := hcomm
  · rintro ⟨i, u, hu, rfl⟩
    have hy : y ∈ Subgroup.closure ((A : Set G) ∪ {y}) :=
      Subgroup.subset_closure (Set.mem_union_right _ (Set.mem_singleton y))
    have hu' : u ∈ Subgroup.closure ((A : Set G) ∪ {y}) :=
      Subgroup.subset_closure (Set.mem_union_left _ hu)
    exact mul_mem (zpow_mem hy i) hu'

theorem conj_mem_closure_of_gens {G : Type*} [Group G] (S : Set G) (W : Subgroup G) (g : G)
    (h : ∀ t ∈ S, g * t * g⁻¹ ∈ W) {z : G} (hz : z ∈ Subgroup.closure S) :
    g * z * g⁻¹ ∈ W := by
  have hle : Subgroup.closure S ≤ W.comap (MulEquiv.toMonoidHom (MulAut.conj g)) := by
    rw [Subgroup.closure_le]
    intro t ht
    exact h t ht
  exact hle hz

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
