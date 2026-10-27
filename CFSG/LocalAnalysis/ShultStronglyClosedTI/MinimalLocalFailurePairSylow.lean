module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairSylowEscape
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairConfinement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalFixedSet
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G] [Finite G]

theorem pairSylow_full_fixed_points
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hgen : FullPointPairGeneration H z)
    (p : ℕ) (hp : p.Prime) (hpdiv : p ∣ Nat.card (conjugacyWithin H z))
    (R : Sylow p G) : Nat.card (pointFixedSet H (R : Subgroup G)) = 2 := by
  have hodd : Odd p := (minimalLocalFailure_point_class_card_odd_and_gt_one h).1.of_dvd_nat
    hpdiv
  by_contra hbad
  obtain ⟨P, hP, hPH, hzP, hmotion, hescape⟩ :=
    pairSylow_bad_sylow_inverted_centralizer_escape h hgen p hp hodd ⟨R, hbad⟩
  have hPz : CFSG.conjugate P z = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normalizer (P : Set G)).inv_mem hzP)
  exact hescape (minimalLocalFailurePairConfinement h hgen p hp hodd hpdiv
    P hPH hP hPz hmotion.symm.le)

theorem pairSylow_double_transitivity_of_full_fixed_points
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (p : ℕ) (hp : p.Prime) (hodd : Odd p)
    (hfixed : ∀ R : Sylow p G, Nat.card (pointFixedSet H (R : Subgroup G)) = 2) :
    ∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d := by
  let : Fact p.Prime := ⟨hp⟩
  let R : Sylow p G := default
  let C := rightCosetStabilizer H (rightCosetMk H 1)
  let Q : Sylow p C := default
  obtain ⟨A, hA⟩ := point_sylow_is_ambient_of_two_fixed_points H (R : Subgroup G)
    p hp hodd R.isPGroup' (hfixed R) (rightCosetMk H 1) Q
  let P := (Q : Subgroup C).map C.subtype
  have hAP : (A : Subgroup G) = P := hA
  have hPH : P ≤ H := by
    have hPC : P ≤ C := Subgroup.map_subtype_le _
    simpa only [C, rightCosetStabilizer_base] using hPC
  have hP : IsPGroup p P := Q.isPGroup'.map C.subtype
  have hPfixed : Nat.card (pointFixedSet H P) = 2 := by
    rw [← hAP]
    exact hfixed A
  have hmax : IsMaximalTwoPointPrime H p P := by
    intro D hD hPD _
    exact (A.is_maximal' hD (by rwa [hAP])).trans hAP
  obtain ⟨T, hzT, hzcenter⟩ := h.central_sylow
  exact maximal_two_fixed_points_doubly_transitive h.local_datum T hzT hzcenter p hp
    hodd hP hPH hPfixed hmax

theorem minimalLocalFailurePairSylow
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hgen : FullPointPairGeneration H z) :
    Odd (Nat.card (conjugacyWithin H z)) ∧
      1 < Nat.card (conjugacyWithin H z) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card (conjugacyWithin H z) →
        ∀ R : Sylow p G, Nat.card (pointFixedSet H (R : Subgroup G)) = 2) ∧
      (∀ a b c d : pointRightCosetSpace H, a ≠ b → c ≠ d →
        ∃ g : G, pointRightCosetMul H a g = c ∧ pointRightCosetMul H b g = d) := by
  obtain ⟨hodd, hgt⟩ := minimalLocalFailure_point_class_card_odd_and_gt_one h
  have hfixed := pairSylow_full_fixed_points h hgen
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hgt)
  exact ⟨hodd, hgt, hfixed,
    pairSylow_double_transitivity_of_full_fixed_points h p hp (hodd.of_dvd_nat hpdiv)
      (hfixed p hp hpdiv)⟩

end CFSG.ShultStronglyClosedTI
