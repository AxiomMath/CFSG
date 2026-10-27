module

import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerivedLinear
public import CFSG.RankThree.PartTwo.KFacts.K72L3Linear
public import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
public import CFSG.RankThree.PartTwo.Sec8.Notation

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag

theorem commutator_mem_of_forall_eq_mul {G : Type*} [Group G] {N : Subgroup G} [hN : N.Normal]
    {R : Set G} (hR : ∀ x ∈ R, ∀ y ∈ R, Commute x y)
    (hG : ∀ g : G, ∃ d ∈ N, ∃ r ∈ R, g = d * r) (σ τ : G) : σ * τ * σ⁻¹ * τ⁻¹ ∈ N := by
  obtain ⟨d, hd, r, hr, rfl⟩ := hG σ
  obtain ⟨d', hd', r', hr', rfl⟩ := hG τ
  have hc : r * r' = r' * r := hR r hr r' hr'
  have key : d * r * (d' * r') * (d * r)⁻¹ * (d' * r')⁻¹ =
      d * (r * d' * r⁻¹) * (r' * d⁻¹ * r'⁻¹) * d'⁻¹ :=
    calc _ = d * (r * d' * r⁻¹) * (r * r' * r⁻¹ * d⁻¹ * r'⁻¹) * d'⁻¹ := by group
      _ = _ := by rw [hc]; group
  rw [key]
  exact mul_mem (mul_mem (mul_mem hd (hN.conj_mem _ hd' r)) (hN.conj_mem _ (inv_mem hd) r'))
    (inv_mem hd')

theorem isInnerAut_commutator_of_mulEquiv_projSL {K : Type} [Field K] [Finite K] {X : Type}
    [Group X] (hK : Nat.card K % 3 = 2) (e : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 K)
    (σ τ : MulAut X) : IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 K
  rw [← isInnerAut_congr (e.trans φ), map_mul, map_mul, map_mul, map_inv, map_inv]
  exact isInnerAut_of_mem_linearAutGroup hK
    (OuterDerived.commutator_mem_linearAutGroup le_rfl _ _)

section Unitary

variable {p f : ℕ} {K : Type} [Field K]

theorem commutator_mem_psuConj_range (h : UnitaryFieldData p f K) (hq2 : 2 < p ^ f)
    (σ τ : MulAut (unitaryPSU h 3)) : σ * τ * σ⁻¹ * τ⁻¹ ∈ (psuConj h).range := by
  have := h.finite
  have : (psuConj h).range.Normal := (stdPinnedPSU3_stable (h := h) hq2).normal
  refine commutator_mem_of_forall_eq_mul (R := Set.range (psuField h)) (fun x hx y hy => ?_)
    (fun g => ?_) σ τ
  · obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    change psuField h s * psuField h t = psuField h t * psuField h s
    rw [← map_mul, ← map_mul, ringAut_mul_comm K s t]
  · obtain ⟨A, s, rfl⟩ := exists_psuConj_mul_psuField hq2 g
    exact ⟨_, ⟨A, rfl⟩, _, ⟨s, rfl⟩, rfl⟩

theorem isInnerAut_commutator_of_mulEquiv_unitaryPSU {X : Type} [Group X]
    (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) (hq2 : 2 < p ^ f)
    (e : X ≃* unitaryPSU h 3) (σ τ : MulAut X) : IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  rw [← isInnerAut_congr e, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact isInnerAut_of_mem_psuConj_range h hq (commutator_mem_psuConj_range h hq2 _ _)

end Unitary

theorem isInnerAut_commutator_of_isoLThreeMinusPi {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : 1 ≤ n) (hX : Sec8.IsoLThreeMinusPi X 2 (3 * n)) (σ τ : MulAut X) :
    IsInnerAut (σ * τ * σ⁻¹ * τ⁻¹) := by
  have hq2 : 2 < 2 ^ (3 * n) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * n))
  rcases hX with ⟨hq, ⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩
  · have h : UnitaryFieldData 2 (3 * n) (GaloisField 2 (2 * (3 * n))) :=
      ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
    obtain ⟨φ⟩ := nonempty_unitaryPSU_mulEquiv_projSU h
    exact isInnerAut_commutator_of_mulEquiv_unitaryPSU h hq hq2 (e.trans φ.symm) σ τ
  · exact isInnerAut_commutator_of_mulEquiv_projSL
      (by rwa [GaloisField.card 2 (3 * n) (by omega)]) e σ τ

end CFSG.RankThree.PartTwo.KFacts
