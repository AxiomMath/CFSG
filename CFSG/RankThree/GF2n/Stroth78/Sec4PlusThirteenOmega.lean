module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEight
public import CFSG.LargeExtraspecial.A2ModNaturalPlusFour

import CFSG.RankThree.GF2n.Stroth78.Sec4PlusTenOmega
import CFSG.LargeExtraspecial.A2ModNaturalOmegaFix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}


theorem exists_natural_pOmegaPlus_four (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hX : CFSG.Blueprint.LieModel ↥(Xsub S a) .POmegaPlus 4 2 1) :
    ∃ (φ : ↥(Xsub S a) ≃* ↥(StatedOmega (StatedQuadPlus 4 (ZMod 2))))
      (π : Additive (QbarOf S) →ₗ[ZMod 2] (Fin 4 ⊕ Fin 4 → ZMod 2)),
      (CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤).map π = ⊤ ∧
      CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤ ⊓ LinearMap.ker π = ⊥ ∧
      (∀ x, ∀ v ∈ CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤, π (rhoX S a x v) =
        ((φ x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2))
          *ᵥ π v) ∧
      (∀ v ∈ CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤,
        StatedQuadPlus 4 (ZMod 2) (π v) = qS S v) := by
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  exact CFSG.LargeExtraspecial.A2Mod.exists_natural_pOmegaPlus_four (rootClass_Xsub S h h217 h34)
    (a2Action_Xsub S a) hX

theorem not_lieModel_pOmegaPlus_four_of_card_ZQ_eq_four (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) (hZ : Nat.card ↥(ZQ z) = 4) :
    ¬ CFSG.Blueprint.LieModel ↥(Xsub S a) .POmegaPlus 4 2 1 := by
  intro hX
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  obtain ⟨φ, π, -, hinj, hπ, hQ⟩ := exists_natural_pOmegaPlus_four S h h217 h34 hX
  obtain ⟨α, hαD, haL, hnfix, hcomm⟩ := exists_alpha_of_card_ZQ_eq_four S h h217 h34 hZ
  have ha0 : aVec S h.mem_Q ≠ 0 := fun h0 => hnfix fun x => by rw [h0, map_zero]
  refine CFSG.LargeExtraspecial.A2Mod.false_of_commute_of_natural_omega (a2Action_Xsub S a)
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 4 (ZMod 2)) (by decide)
    (CFSG.LieType.Universal.Spin.coe_quadPlus 4 (ZMod 2)) φ π hinj hπ hQ hαD haL ha0
    fun y hy3 hfix => hcomm y ?_ hfix
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy3) with h1 | h1 <;>
    rw [h1] <;> decide

end CFSG.RankThree.GF2n.Stroth78
