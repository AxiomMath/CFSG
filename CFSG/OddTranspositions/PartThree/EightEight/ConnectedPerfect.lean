module

public import CFSG.Timmesfeld.Bridge.Asc72Basic
public import CFSG.Timmesfeld.Closure.MinCex
public import CFSG.OddTranspositions.HalphaQuotient

import CFSG.OddTranspositions.PartThree.Nine.ThreeSplit
import CFSG.Timmesfeld.Bridge.Asc72Local
import CFSG.Timmesfeld.Special.Basic
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X] {E : Set X}

theorem sq_mul_sq_mem_commutator {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (ha2 : a ^ 2 ∈ ⁅H, H⁆) (hb2 : b ^ 2 ∈ ⁅H, H⁆) :
    (a * b) ^ 2 ∈ ⁅H, H⁆ := by
  let π : G →* G ⧸ ⁅H, H⁆ := QuotientGroup.mk' ⁅H, H⁆
  have hcomm : Commute (π a) (π b) := by
    rw [commute_iff_eq, ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff (⁅a, b⁆)).mpr
      (Subgroup.commutator_mem_commutator ha hb)
  have ha2' : π (a ^ 2) = 1 := (QuotientGroup.eq_one_iff (a ^ 2)).mpr ha2
  have hb2' : π (b ^ 2) = 1 := (QuotientGroup.eq_one_iff (b ^ 2)).mpr hb2
  have hsq : π ((a * b) ^ 2) = 1 := by
    rw [map_pow, map_mul, hcomm.mul_pow 2, ← map_pow, ← map_pow, ha2', hb2', mul_one]
  exact (QuotientGroup.eq_one_iff ((a * b) ^ 2)).mp hsq

theorem sq_mul_sq_mem_commutator_of_mul {G : Type*} [Group G] {H : Subgroup G} [H.Normal]
    {d e f : G} (he : e * e = 1) (hde : d * e ∈ H) (hef : e * f ∈ H)
    (hde2 : (d * e) ^ 2 ∈ ⁅H, H⁆) (hef2 : (e * f) ^ 2 ∈ ⁅H, H⁆) :
    (d * f) ^ 2 ∈ ⁅H, H⁆ := by
  have hdf : d * f = (d * e) * (e * f) := by
    rw [mul_assoc, ← mul_assoc e, he, one_mul]
  rw [hdf]
  exact sq_mul_sq_mem_commutator hde hef hde2 hef2

omit [Finite X] in
theorem sq_mul_mem_commutator_commutator_of_commRel (hS : Setup X E) {b c : X}
    (hbc : CommRel E b c) : (b * c) ^ 2 ∈ ⁅commutator X, commutator X⁆ := by
  have hb : b * b = 1 := hS.oddT.mul_self_eq_one hbc.1
  have hc : c * c = 1 := hS.oddT.mul_self_eq_one hbc.2.1
  have hsq : (b * c) ^ 2 = 1 := by
    rw [hbc.2.2.mul_pow 2, pow_two b, pow_two c, hb, hc, mul_one]
  rw [hsq]
  exact Subgroup.one_mem _

omit [Finite X] in
theorem sq_mul_mem_commutator_commutator_of_reach (hS : Setup X E) {d e : X} (hd : d ∈ E)
    (h : Reach E d e) : (d * e) ^ 2 ∈ ⁅commutator X, commutator X⁆ := by
  induction h with
  | refl =>
      rw [hS.oddT.mul_self_eq_one hd]
      simp
  | tail _ hbc ih =>
      exact sq_mul_sq_mem_commutator_of_mul (H := commutator X)
        (hS.oddT.mul_self_eq_one hbc.1)
        (hS.mul_mem_commutator hd hbc.1)
        (hS.mul_mem_commutator hbc.1 hbc.2.1)
        ih (sq_mul_mem_commutator_commutator_of_commRel hS hbc)

theorem commutator_le_commutator_commutator_of_connected (hS : Setup X E)
    (hconn : ¬ Disconnected E) : commutator X ≤ ⁅commutator X, commutator X⁆ := by
  have hreach : ∀ d ∈ E, ∀ e ∈ E, Reach E d e :=
    fun d hd e he => reach_of_not_disconnected hconn hd he
  let π : X →* X ⧸ ⁅commutator X, commutator X⁆ := QuotientGroup.mk' ⁅commutator X, commutator X⁆
  have hcomm : ∀ d ∈ E, ∀ e ∈ E, Commute (π d) (π e) := by
    intro d hd e he
    rw [commute_iff_eq, ← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
    refine (QuotientGroup.eq_one_iff (⁅d, e⁆)).mpr ?_
    rw [Special.commutatorElement_eq_mul_sq
      (hS.oddT.mul_self_eq_one hd) (hS.oddT.mul_self_eq_one he)]
    exact sq_mul_mem_commutator_commutator_of_reach hS hd (hreach d hd e he)
  have hpair : (π '' E).Pairwise Commute := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨e, he, rfl⟩ _
    exact hcomm d hd e he
  have hclosure : Subgroup.closure (π '' E) = ⊤ := by
    rw [← MonoidHom.map_closure π E, hS.gen,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective ⁅commutator X, commutator X⁆)]
  have htop : IsMulCommutative (⊤ : Subgroup (X ⧸ ⁅commutator X, commutator X⁆)) := by
    have h := Subgroup.isMulCommutative_closure hpair
    rwa [hclosure] at h
  have hQ : IsMulCommutative (X ⧸ ⁅commutator X, commutator X⁆) :=
    Function.Surjective.isMulCommutative
      (f := Subgroup.subtype (⊤ : Subgroup (X ⧸ ⁅commutator X, commutator X⁆)))
      (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩) htop
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le
    (N := ⁅commutator X, commutator X⁆)).mp hQ

theorem derivedSeries_one_eq_two_of_not_disconnected {X : Type*} [Group X] [Finite X]
    {E : Set X} (hS : CFSG.Timmesfeld.Bridge.Asc72.Setup X E)
    (hconn : ¬ CFSG.Timmesfeld.Connectivity.Disconnected E) :
    derivedSeries X 1 = derivedSeries X 2 := by
  have hle := commutator_le_commutator_commutator_of_connected hS hconn
  rw [derivedSeries_one, derivedSeries_succ X 1, derivedSeries_one]
  exact le_antisymm hle (Subgroup.commutator_le_self (commutator X))

end CFSG.OddTranspositions.PartThree
