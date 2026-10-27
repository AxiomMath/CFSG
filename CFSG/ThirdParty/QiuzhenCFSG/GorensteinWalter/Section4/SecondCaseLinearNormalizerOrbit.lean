module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearLineCard
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The normalizer orbit of the selected line
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The `N_U(A)`-orbit of `P` injects into the ambient conjugates of `P`
contained in `A`.  In particular, its relative index over `N_U(P)` is at
most the equation-(8) conjugate count. -/
public theorem secondCase_linear_normalizerOrbit_le_conjugateCount
    {G : Type u} [Group G] [Finite G]
    {U P A : Subgroup G}
    (hPleA : P ≤ A) :
    (normalizerIn U P).relIndex (normalizerIn U A) ≤ conjugateCount P A := by
  classical
  let NA : Subgroup G := normalizerIn U A
  let NP : Subgroup G := normalizerIn U P
  let C : Type u := {X : Subgroup G // X ≤ A ∧ IsConjugateSubgroup P X}
  have hconj_leA (a : NA) : conjugateSubgroup P (a : G) ≤ A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
    have haN : (a : G) ∈ Subgroup.normalizer (A : Set G) := a.2.2
    exact (Subgroup.mem_normalizer_iff.mp haN (p : G)).1 (hPleA hp)
  let f : (NA : Type u) ⧸ (NP.subgroupOf NA) → C :=
    Quotient.lift (s := QuotientGroup.leftRel (NP.subgroupOf NA))
      (fun a : NA => ⟨conjugateSubgroup P (a : G),
        hconj_leA a, ⟨a, rfl⟩⟩)
      (by
        intro a b hab
        apply Subtype.ext
        apply conjugate_subgroup_eq_of_left_inv_mem_normalizer
        have hab' : (a : G)⁻¹ * (b : G) ∈ Subgroup.normalizer (P : Set G) := by
          simpa [NP, normalizerIn] using
            (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hab)).2
        exact hab')
  have hf_inj : Function.Injective f := by
    intro x y hxy
    revert hxy
    refine Quotient.inductionOn₂ x y ?_
    intro a b hab
    have hEq : conjugateSubgroup P (a : G) = conjugateSubgroup P (b : G) := by
      simpa [f] using congrArg (fun z : C => z.1) hab
    have hN : (a : G)⁻¹ * (b : G) ∈ Subgroup.normalizer (P : Set G) :=
      left_inv_mem_normalizer_of_conjugate_subgroup_eq hEq
    have hU : (a : G)⁻¹ * (b : G) ∈ U :=
      U.mul_mem (U.inv_mem a.2.1) b.2.1
    have hNP : (a : G)⁻¹ * (b : G) ∈ NP := ⟨hU, hN⟩
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr
      (Subgroup.mem_subgroupOf.mpr hNP))
  have hcard : Nat.card ((NA : Type u) ⧸ (NP.subgroupOf NA)) ≤ Nat.card C :=
    Nat.card_le_card_of_injective f hf_inj
  have hsource : Nat.card ((NA : Type u) ⧸ (NP.subgroupOf NA)) =
      (normalizerIn U P).relIndex (normalizerIn U A) := by
    change Nat.card (NA ⧸ (NP.subgroupOf NA)) = (NP.subgroupOf NA).index
    exact (Subgroup.index_eq_card (NP.subgroupOf NA)).symm
  have htarget : Nat.card C = conjugateCount P A := by
    rfl
  rw [hsource, htarget] at hcard
  exact hcard

end CFSG.GorensteinWalter
