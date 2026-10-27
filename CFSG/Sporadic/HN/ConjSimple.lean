module

public import CFSG.GroupActions.PrimitiveNormalTransitive
public import CFSG.GroupActions.StabilizerFactorization
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.Sporadic.F5

theorem orderOf_conj_dvd {G : Type*} [Group G] (g b : G) : orderOf (g⁻¹ * b * g) ∣ orderOf b := by
  apply orderOf_dvd_of_pow_eq_one
  have h := conj_pow (a := g⁻¹) (b := b) (i := orderOf b)
  rw [inv_inv] at h
  rw [h, pow_orderOf_eq_one, mul_one, inv_mul_cancel]

theorem isSimpleGroup_of_primitive_conj_product
    {G Ω : Type*} [Group G] [Finite G] [Finite Ω] [MulAction G Ω] [FaithfulSMul G Ω]
    [MulAction.IsPreprimitive G Ω] (hΩ : 2 ≤ Nat.card Ω) (a b g : G)
    (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (ω : Ω)
    (hab : (orderOf a).Coprime (orderOf b))
    (hst : (orderOf (a * (g⁻¹ * b * g))).Coprime (Nat.card (MulAction.stabilizer G ω))) :
    IsSimpleGroup G := by
  classical
  let _ : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (Nat.lt_of_succ_le hΩ)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Ω
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G x y
  have hh_ne : h ≠ 1 := by
    intro e
    apply hxy
    simpa [e] using hh
  let _ : Nontrivial G := ⟨⟨h, 1, hh_ne⟩⟩
  rw [isSimpleGroup_iff]
  refine ⟨inferInstance, ?_⟩
  intro N hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  right
  let _ : N.Normal := hN
  let _ : MulAction.IsPretransitive N Ω :=
    CFSG.GroupActions.isPretransitive_of_normal_ne_bot N hNbot
  let φ : G →* G ⧸ N := QuotientGroup.mk' N
  have hcard : Nat.card (G ⧸ N) ∣ Nat.card (MulAction.stabilizer G ω) :=
    CFSG.GroupActions.quotient_card_dvd_stabilizer_card N ω
  have hprod : φ (a * (g⁻¹ * b * g)) = 1 := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes hst (orderOf_map_dvd φ _)
      ((orderOf_dvd_natCard (φ _)).trans hcard)
  have hinv : φ a = (φ (g⁻¹ * b * g))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa using hprod
  have hconj : φ (g⁻¹ * b * g) = (φ g)⁻¹ * φ b * φ g := by simp
  have ha : φ a = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hab (orderOf_map_dvd φ a)
    rw [hinv, orderOf_inv, hconj]
    exact (orderOf_conj_dvd (φ g) (φ b)).trans (orderOf_map_dvd φ b)
  have hb : φ b = 1 := by
    have h1 : φ (g⁻¹ * b * g) = 1 := by
      rw [map_mul, ha, one_mul] at hprod
      exact hprod
    rw [hconj] at h1
    have h2 : φ b * φ g = φ g := by
      calc φ b * φ g = φ g * ((φ g)⁻¹ * φ b * φ g) := by group
        _ = φ g := by rw [h1, mul_one]
    exact mul_eq_right.mp h2
  have haN : a ∈ N := (QuotientGroup.eq_one_iff a).mp ha
  have hbN : b ∈ N := (QuotientGroup.eq_one_iff b).mp hb
  apply top_le_iff.mp
  rw [← hgen]
  apply (Subgroup.closure_le N).mpr
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact haN
  · exact hbN

end CFSG.Sporadic.F5
