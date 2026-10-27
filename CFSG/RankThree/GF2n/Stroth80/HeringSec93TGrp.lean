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

namespace CFSG.RankThree.GF2n.Stroth80.HS9

variable {G : Type} [Group G] [Finite G]

theorem card_sup_mul_card_inf_of_le_normalizer {A F : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (F : Set G)) :
    Nat.card ↥(A ⊔ F) * Nat.card ↥(A ⊓ F) = Nat.card ↥A * Nat.card ↥F := by
  haveI : (F.subgroupOf (A ⊔ F)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hA
  have h3 : A.subgroupOf (A ⊔ F) ⊔ F.subgroupOf (A ⊔ F) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : A ≤ A ⊔ F) (le_sup_right : F ≤ A ⊔ F)]
    exact Subgroup.subgroupOf_self _
  have key : F.relIndex (A ⊔ F) = F.relIndex A :=
    calc F.relIndex (A ⊔ F) = (F.subgroupOf (A ⊔ F)).relIndex ⊤ :=
          (Subgroup.relIndex_top_right _).symm
      _ = (F.subgroupOf (A ⊔ F)).relIndex
            (A.subgroupOf (A ⊔ F) ⊔ F.subgroupOf (A ⊔ F)) := by
          rw [h3]
      _ = (F.subgroupOf (A ⊔ F)).relIndex (A.subgroupOf (A ⊔ F)) :=
          Subgroup.relIndex_sup_right _ _
      _ = F.relIndex A := Subgroup.relIndex_subgroupOf (le_sup_left : A ≤ A ⊔ F)
  have e1 : F.relIndex (A ⊔ F) * Nat.card ↥(F ⊓ (A ⊔ F)) = Nat.card ↥(A ⊔ F) :=
    Subgroup.relIndex_mul_card F (A ⊔ F)
  have e2 : F.relIndex A * Nat.card ↥(F ⊓ A) = Nat.card ↥A :=
    Subgroup.relIndex_mul_card F A
  rw [inf_eq_left.mpr (le_sup_right : F ≤ A ⊔ F), key] at e1
  rw [inf_comm F A] at e2
  rw [← e1, ← e2]
  ring

theorem relIndex_mul_card_eq_card_sup {A F : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (F : Set G)) :
    F.relIndex A * Nat.card ↥F = Nat.card ↥(A ⊔ F) := by
  have h1 := card_sup_mul_card_inf_of_le_normalizer hA
  have h2 : F.relIndex A * Nat.card ↥(F ⊓ A) = Nat.card ↥A := Subgroup.relIndex_mul_card F A
  rw [inf_comm] at h1
  have hpos : 0 < Nat.card ↥(F ⊓ A) := Nat.card_pos
  have : Nat.card ↥(A ⊔ F) * Nat.card ↥(F ⊓ A) =
      (F.relIndex A * Nat.card ↥F) * Nat.card ↥(F ⊓ A) := by
    rw [h1, ← h2]
    ring
  exact (Nat.eq_of_mul_eq_mul_right hpos this).symm

theorem exists_conj_mem_of_odd_index {X P P' : Subgroup G} (hPX : P ≤ X) (hP'X : P' ≤ X)
    (hP2 : IsPGroup 2 ↥P) (hP'2 : IsPGroup 2 ↥P') {m : ℕ} (hm : Odd m)
    (hcard : Nat.card ↥X = Nat.card ↥P * m) : ∃ g ∈ X, ∀ x ∈ P', g⁻¹ * x * g ∈ P := by
  have hP₀2 : IsPGroup 2 ↥(P.subgroupOf X) := hP2.comap_subtype (K := X)
  have hP'₀2 : IsPGroup 2 ↥(P'.subgroupOf X) := hP'2.comap_subtype (K := X)
  have hPcard : Nat.card ↥(P.subgroupOf X) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv
  have hPidx : (P.subgroupOf X).index = m := by
    have h1 := Subgroup.card_mul_index (H := P.subgroupOf X)
    rw [hPcard, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥P)) h1
  have hnd : ¬ 2 ∣ (P.subgroupOf X).index := by
    rw [hPidx]
    obtain ⟨k, hk⟩ := hm
    rintro ⟨c, hc⟩
    omega
  let S₀ : Sylow 2 ↥X := hP₀2.toSylow hnd
  haveI : Finite (Sylow 2 ↥X) :=
    Finite.of_injective (fun Q : Sylow 2 ↥X => (Q : Set ↥X)) fun Q R h => SetLike.coe_injective h
  obtain ⟨S', hS'⟩ := hP'₀2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X S₀ S'
  refine ⟨(g : G), g.2, fun x hx => ?_⟩
  have hy : (⟨x, hP'X hx⟩ : ↥X) ∈ (S' : Subgroup ↥X) :=
    hS' (Subgroup.mem_subgroupOf.mpr hx)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    MulAut.smul_def, MulAut.conj_inv_apply] at hy
  have hy' : g⁻¹ * (⟨x, hP'X hx⟩ : ↥X) * g ∈ P.subgroupOf X := hy
  simpa using Subgroup.mem_subgroupOf.mp hy'

theorem card_dvd_of_isPGroup_of_odd {X P F : Subgroup G} (hPX : P ≤ X) (hP2 : IsPGroup 2 ↥P)
    (hF2 : IsPGroup 2 ↥F) {q m : ℕ} (hq : ∃ e : ℕ, q = 2 ^ e) (hm : Odd m)
    (hcard : Nat.card ↥X = Nat.card ↥F * (q * m)) : Nat.card ↥P ∣ Nat.card ↥F * q := by
  have hdvd : Nat.card ↥P ∣ Nat.card ↥F * (q * m) := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hPX
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP2
  have hcop : Nat.Coprime (Nat.card ↥P) m := by
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)
  rw [← mul_assoc] at hdvd
  exact hcop.dvd_of_dvd_mul_right hdvd

end CFSG.RankThree.GF2n.Stroth80.HS9
