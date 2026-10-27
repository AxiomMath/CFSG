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

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem aux_CardCent_iff {G : Type*} [Group G] (a b c : G) :
    a * c * a⁻¹ = b * c * b⁻¹ ↔ (a⁻¹ * b) * c = c * (a⁻¹ * b) := by
  have hb : b = a * (a⁻¹ * b) := (mul_inv_cancel_left a b).symm
  generalize hg : a⁻¹ * b = g at hb ⊢
  rw [hb]
  have key : a * g * c * (a * g)⁻¹ = a * (g * c * g⁻¹) * a⁻¹ := by
    simp only [mul_inv_rev, mul_assoc]
  rw [key, mul_left_inj, mul_right_inj]
  exact ⟨fun h => mul_inv_eq_iff_eq_mul.1 h.symm, fun h => (mul_inv_eq_iff_eq_mul.2 h).symm⟩

theorem card_le_three_mul_card_centralizer {G : Type*} [Group G] [Finite G]
    (S : Subgroup G) (c : G) (T : Finset G) (hT : T.card ≤ 3)
    (hS : ∀ s ∈ S, s * c * s⁻¹ ∈ T) :
    Nat.card S ≤ 3 * Nat.card (S ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) := by
  set C : Subgroup G := S ⊓ Subgroup.centralizer ({c} : Set G) with hC
  set C' : Subgroup S := C.subgroupOf S with hC'
  have hle : C ≤ S := by
    rw [hC]
    exact inf_le_left
  have hmem : ∀ x : S, x ∈ C' ↔ (x : G) * c = c * (x : G) := by
    intro x
    rw [hC', Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hcard : Nat.card S = Nat.card (S ⧸ C') * Nat.card C' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup C'
  have hcardC : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hquot : Nat.card (S ⧸ C') ≤ 3 := by
    let g : S → T := fun s => ⟨(s : G) * c * (s : G)⁻¹, hS (s : G) s.2⟩
    have hg : ∀ a b : S, a⁻¹ * b ∈ C' → g a = g b := by
      intro a b hab
      apply Subtype.ext
      have hab' := (hmem (a⁻¹ * b)).1 hab
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hab'
      exact (aux_CardCent_iff (a : G) (b : G) c).2 hab'
    let φ : S ⧸ C' → T :=
      Quotient.lift g (fun a b hab => hg a b (QuotientGroup.leftRel_apply.1 hab))
    have hinj : Function.Injective φ := by
      intro x y hxy
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      have h1 : g a = g b := hxy
      have h2 : (a : G) * c * (a : G)⁻¹ = (b : G) * c * (b : G)⁻¹ := congrArg Subtype.val h1
      apply QuotientGroup.eq.2
      rw [hmem]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (aux_CardCent_iff (a : G) (b : G) c).1 h2
    have hle' : Nat.card (S ⧸ C') ≤ Nat.card T := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_eq_finsetCard] at hle'
    exact le_trans hle' hT
  rw [hcard, hcardC]
  exact Nat.mul_le_mul_right _ hquot

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
