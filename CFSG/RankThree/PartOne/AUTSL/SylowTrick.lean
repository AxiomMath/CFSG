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

namespace CFSG.RankThree.PartOne.AUTSL

open scoped _root_.Classical Pointwise

section SylowTrick

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
private theorem card_subgroupOf_of_le {T H : Subgroup X} (h : T ≤ H) :
    Nat.card (T.subgroupOf H) = Nat.card T :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem exists_conj_eq_of_sylow_trick {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime) (hpq : p ≠ q)
    {S B : Subgroup X} (hS : IsPGroup q S) (hB : IsPGroup p B)
    (hBS : B ≤ Subgroup.normalizer (S : Set X)) (x : MulAut X)
    (hx : ∀ b ∈ B, b⁻¹ * x b ∈ S) : ∃ s ∈ S, ∀ b ∈ B, x b = s * b * s⁻¹ := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := q) (G := S)).1 hS
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := B)).1 hB
  have hcop : Nat.Coprime (Nat.card S) (Nat.card B) := by
    rw [hm, hk]
    exact Nat.Coprime.pow m k ((Nat.coprime_primes hq hp.out).2 hpq.symm)
  set H : Subgroup X := S ⊔ B with hH
  have hSH : S ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (S : Set X) := sup_le Subgroup.le_normalizer hBS
  set S₁ : Subgroup H := S.subgroupOf H with hS₁def
  set B₁ : Subgroup H := B.subgroupOf H with hB₁def
  have hS₁ : S₁.Normal := by
    refine (Subgroup.normal_subgroupOf_iff hSH).2 fun s h hs hh => ?_
    exact (Subgroup.mem_normalizer_iff.1 (hHN hh) s).1 hs
  have hdisj : Disjoint S B := Subgroup.disjoint_of_coprime_natCard hcop
  have hdisj₁ : Disjoint S₁ B₁ := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hS₁def, hB₁def, card_subgroupOf_of_le hSH, card_subgroupOf_of_le hBH]
    exact hcop
  have hsup₁ : S₁ ⊔ B₁ = ⊤ := by
    rw [hS₁def, hB₁def, ← Subgroup.subgroupOf_sup hSH hBH, ← hH, Subgroup.subgroupOf_self]
  have hmul : (S₁ : Set H) * (B₁ : Set H) = Set.univ := by
    rw [← Subgroup.normal_mul, hsup₁]
    rfl
  have hcompl : S₁.IsComplement' B₁ :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj₁ hmul
  have hcardH : Nat.card H = Nat.card S * Nat.card B := by
    rw [← hcompl.card_mul_card, hS₁def, hB₁def, card_subgroupOf_of_le hSH,
      card_subgroupOf_of_le hBH]
  have hfact : (Nat.card H).factorization p = k := by
    rw [hcardH, hm, hk, Nat.factorization_mul (pow_ne_zero _ hq.ne_zero)
      (pow_ne_zero _ hp.out.ne_zero), Finsupp.add_apply, hp.out.factorization_pow,
      hq.factorization_pow, Finsupp.single_apply, Finsupp.single_eq_same]
    simp [hpq.symm]
  have hxB : B.map x.toMonoidHom ≤ H := by
    rintro _ ⟨b, hb, rfl⟩
    have h1 : x b = b * (b⁻¹ * x b) := by group
    change x b ∈ H
    rw [h1]
    exact H.mul_mem (hBH hb) (hSH (hx b hb))
  set B₂ : Subgroup H := (B.map x.toMonoidHom).subgroupOf H with hB₂def
  have hcardB₂ : Nat.card B₂ = Nat.card B := by
    rw [hB₂def, card_subgroupOf_of_le hxB]
    exact Subgroup.card_map_of_injective x.injective
  have hP : Nat.card B₁ = p ^ (Nat.card H).factorization p := by
    rw [hfact, hB₁def, card_subgroupOf_of_le hBH, hk]
  have hP' : Nat.card B₂ = p ^ (Nat.card H).factorization p := by
    rw [hfact, hcardB₂, hk]
  let P : Sylow p H := Sylow.ofCard B₁ hP
  let P' : Sylow p H := Sylow.ofCard B₂ hP'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P P'
  have hsb : g ∈ (S₁ : Set H) * (B₁ : Set H) := by rw [hmul]; exact Set.mem_univ g
  obtain ⟨s₁, hs₁, b₁, hb₁, hgsb⟩ := Set.mem_mul.1 hsb
  refine ⟨(s₁ : X), hs₁, fun b hb => ?_⟩
  have hxbH : x b ∈ H := hxB ⟨b, hb, rfl⟩
  have hmem : (⟨x b, hxbH⟩ : H) ∈ (P' : Subgroup H) := by
    show (⟨x b, hxbH⟩ : H) ∈ B₂
    rw [hB₂def, Subgroup.mem_subgroupOf]
    exact ⟨b, hb, rfl⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨b₂, hb₂, hconj⟩ := hmem
  have hb₂B : (b₂ : X) ∈ B := hb₂
  have hb₁B : (b₁ : X) ∈ B := hb₁
  have hxb : x b = (s₁ : X) * ((b₁ : X) * (b₂ : X) * (b₁ : X)⁻¹) * (s₁ : X)⁻¹ := by
    have h1 := congrArg Subtype.val hconj
    rw [MulAut.smul_def, MulAut.conj_apply, ← hgsb] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc] at h1 ⊢
    exact h1.symm
  set b' : X := (b₁ : X) * (b₂ : X) * (b₁ : X)⁻¹ with hb'def
  have hb'B : b' ∈ B := B.mul_mem (B.mul_mem hb₁B hb₂B) (B.inv_mem hb₁B)
  have hc : b⁻¹ * x b ∈ S := hx b hb
  have hsS : (s₁ : X) ∈ S := hs₁
  have hconjS : b⁻¹ * (s₁ : X) * b ∈ S := by
    have := (Subgroup.mem_normalizer_iff.1 (B.inv_mem hb |> hBS) (s₁ : X)).1 hsS
    simpa using this
  have hb'S : b'⁻¹ * b ∈ S := by
    have h2 : b'⁻¹ * b = (s₁ : X)⁻¹ * (b⁻¹ * x b)⁻¹ * (b⁻¹ * (s₁ : X) * b) := by
      have h3 : b' = (s₁ : X)⁻¹ * x b * (s₁ : X) := by
        rw [hxb]; group
      rw [h3]
      group
    rw [h2]
    exact S.mul_mem (S.mul_mem (S.inv_mem hsS) (S.inv_mem hc)) hconjS
  have hb'b : b'⁻¹ * b = 1 := by
    have h4 : b'⁻¹ * b ∈ B := B.mul_mem (B.inv_mem hb'B) hb
    exact Subgroup.disjoint_def.1 hdisj hb'S h4
  have hb'eq : b' = b := by
    have := inv_mul_eq_one.1 hb'b
    exact this
  rw [hxb, hb'eq]

end SylowTrick

end CFSG.RankThree.PartOne.AUTSL
