module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusDefs

import CFSG.LargeExtraspecial.A2ModHubFine
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEight
import CFSG.RankThree.GF2n.Stroth78.Sec4PlusPerfect
import CFSG.Milestones.ASVolI.F4Native
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem false_of_isPerfect_of_index_eq_two {G : Type*} [Group G] [Group.IsPerfect G]
    {M : Subgroup G} (hM : M.index = 2) : False := by
  haveI : M.Normal := Subgroup.normal_of_index_eq_two hM
  have hcard : Nat.card (G ⧸ M) = 2 := hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (G ⧸ M) := isCyclic_of_prime_card hcard
  haveI : Finite (G ⧸ M) := Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial (G ⧸ M) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  haveI : Group.IsPerfect (G ⧸ M) := inferInstance
  exact Group.IsPerfect.not_isMulCommutative (G ⧸ M) inferInstance

section Hub


theorem not_isPerfect_adjointGroup_g2 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ¬ Group.IsPerfect ↥(adjointGroup .G2 K) := by
  intro hP
  haveI : Group.IsPerfect (AdjointQuotient .G2 K) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center ↥(adjointGroup .G2 K)))
      (QuotientGroup.mk'_surjective _)
  exact false_of_isPerfect_of_index_eq_two (CFSG.ASVolI.burnsideF4h_g2_incl_index hK)

theorem Xsub_lieModel_or_psu33_of_threeFourPlus (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) :
    (∃ m, 3 ≤ m ∧ CFSG.Blueprint.LieModel ↥(Xsub S a) .PSL m 2 1) ∨
      (∃ m, 4 ≤ m ∧ CFSG.Blueprint.LieModel ↥(Xsub S a) .POmegaPlus m 2 1) ∨
      (∃ n, 3 ≤ n ∧ CFSG.Blueprint.LieModel ↥(Xsub S a) .PSp n 2 1) ∨
      (∃ n, 4 ≤ n ∧ CFSG.Blueprint.LieModel ↥(Xsub S a) .POmegaMinus n 2 1) ∨
      CFSG.Blueprint.LieModel ↥(Xsub S a) .PSU 3 3 1 := by
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  rcases CFSG.LargeExtraspecial.A2Mod.hub_any_fine (rootClass_Xsub S h h217 h34)
      (a2Action_Xsub S a) with h1 | h1 | h1 | h1 | h1 | ⟨K', _, _, hK, ⟨e⟩⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))
  · exfalso
    haveI : Group.IsPerfect ↥(Xsub S a) :=
      Subgroup.isPerfect_iff.mpr (commutator_Xsub_eq_of_threeFourPlus S h h217 h34)
    haveI : Group.IsPerfect ↥(adjointGroup .G2 K') :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact not_isPerfect_adjointGroup_g2 hK inferInstance

end Hub

end CFSG.RankThree.GF2n.Stroth78
