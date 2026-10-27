module

public import CFSG.RankThree.GF2n.Stroth78.Sec4PlusEight
public import CFSG.LargeExtraspecial.A2ModNaturalMinusFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module Matrix CFSG.ClassicalGroups.Symplectic

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem exists_naturalSeries_psp (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) {m : ℕ} (hm : 4 ≤ m)
    (hX : CFSG.Blueprint.LieModel ↥(Xsub S a) .PSp m 2 1) :
    ∃ (Q₁ Q₂ : Submodule (ZMod 2) (Additive (QbarOf S)))
      (φ : ↥(Xsub S a) ≃* ↥(StatedSp m (ZMod 2)))
      (π : Additive (QbarOf S) →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)),
      Q₁ ≤ Q₂ ∧ CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤ ≤ Q₂ ∧
      (∀ x, ∀ v ∈ Q₁, rhoX S a x v = v) ∧
      Q₂.map π = ⊤ ∧ Q₂ ⊓ LinearMap.ker π = Q₁ ∧
      (∀ x, ∀ v ∈ Q₂, π (rhoX S a x v) =
        ((φ x : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2))
          *ᵥ π v) ∧
      (∀ u ∈ Q₂, ∀ v ∈ Q₂, QuadraticMap.polar (qS S) u v = spForm m (ZMod 2) (π u) (π v)) := by
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  exact CFSG.LargeExtraspecial.A2Mod.exists_naturalSeries_psp (rootClass_Xsub S h h217 h34)
    (a2Action_Xsub S a) hm hX

theorem exists_natural_pOmegaPlus (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) {m : ℕ} (hm : 5 ≤ m)
    (hX : CFSG.Blueprint.LieModel ↥(Xsub S a) .POmegaPlus m 2 1) :
    ∃ (φ : ↥(Xsub S a) ≃* ↥(StatedOmega (StatedQuadPlus m (ZMod 2))))
      (π : Additive (QbarOf S) →ₗ[ZMod 2] (Fin m ⊕ Fin m → ZMod 2)),
      (CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤).map π = ⊤ ∧
      CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤ ⊓ LinearMap.ker π = ⊥ ∧
      (∀ x, ∀ v ∈ CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤, π (rhoX S a x v) =
        ((φ x : GL (Fin m ⊕ Fin m) (ZMod 2)) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (ZMod 2))
          *ᵥ π v) ∧
      (∀ v ∈ CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤,
        StatedQuadPlus m (ZMod 2) (π v) = qS S v) := by
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  exact CFSG.LargeExtraspecial.A2Mod.exists_natural_pOmegaPlus (rootClass_Xsub S h h217 h34)
    (a2Action_Xsub S a) hm hX

theorem exists_natural_pOmegaMinus (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h34 : ThreeFourPlus S a) {m : ℕ} (hm : 4 ≤ m)
    (hX : CFSG.Blueprint.LieModel ↥(Xsub S a) .POmegaMinus m 2 1) :
    ∃ (φ : ↥(Xsub S a) ≃* ↥(StatedOmega (StatedQuadMinus m (ZMod 2) 1 1)))
      (π : Additive (QbarOf S) →ₗ[ZMod 2] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2)),
      (CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤).map π = ⊤ ∧
      CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤ ⊓ LinearMap.ker π = ⊥ ∧
      (∀ x, ∀ v ∈ CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤, π (rhoX S a x v) =
        ((φ x : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2)
            (ZMod 2)) *ᵥ π v) ∧
      (∀ v ∈ CFSG.LargeExtraspecial.A2Mod.commSpaceOf (rhoX S a) ⊤,
        StatedQuadMinus m (ZMod 2) 1 1 (π v) = qS S v) := by
  haveI : FiniteDimensional (ZMod 2) (Additive (QbarOf S)) := Module.Finite.of_finite
  exact CFSG.LargeExtraspecial.A2Mod.exists_natural_pOmegaMinus (rootClass_Xsub S h h217 h34)
    (a2Action_Xsub S a) hm hX

end CFSG.RankThree.GF2n.Stroth78
