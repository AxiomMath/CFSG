module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {W : Type} [CommGroup W]

@[expose] def HJSetup (W : Type) [CommGroup W] [Finite W]
    (Y L : Subgroup (MulAut W)) : Prop :=
  L ≤ Y ∧ (L.subgroupOf Y).Normal ∧ IsSpor ↥L .J2 ∧ IsIrrOn L ⊤ ⊥ ∧ rk W = 12 ∧
    Nat.card Y ∣ 6 * Nat.card L

@[expose] def K_HJLineScalars : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)), HJSetup W Y L →
      ∀ T : Subgroup (MulAut W), T ≤ Y → IsSylowIn 2 T Y →
        ∃ v₁ v₂ : W,
          v₁ ≠ 1 ∧ v₂ ≠ 1 ∧
          (∀ v : W, v ≠ 1 → (∃ l ∈ L, l v = v₁) ∨ (∃ l ∈ L, l v = v₂)) ∧
          (¬ ∃ l ∈ L, l v₁ = v₂) ∧
          Nat.card ↥(MulAction.stabilizer (MulAut W) v₁ ⊓ L) = 2 ^ 7 * 3 ∧
          (MulAction.stabilizer (MulAut W) v₁ ⊓ L) ≤
            L ⊓ Subgroup.normalizer
              ((thompsonJ T : Subgroup (MulAut W)) : Set (MulAut W)) ∧
          Nonempty (↥(MulAction.stabilizer (MulAut W) v₂ ⊓ L) ≃*
            (Multiplicative (ZMod 2 × ZMod 2) × alternatingGroup (Fin 5))) ∧
          (∀ v : W, v ≠ 1 →
            Nat.card ↥(MulAction.stabilizer (MulAut W) v ⊓ L) = 240 →
              ∀ t : MulAut W, t ∈ Y → orderOf t = 2 →
                rk (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) < 6 →
                  rk (commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) = 4 ∧
                    ∀ H : Subgroup W, H ≤ fixV (Subgroup.zpowers t) →
                      H.relIndex (fixV (Subgroup.zpowers t)) = 2 →
                        ∃ l ∈ L, l v ∈ H)

@[expose] def K_HJGammaOne : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Y L : Subgroup (MulAut W)), HJSetup W Y L →
      ∀ T : Subgroup (MulAut W), T ≤ Y → IsSylowIn 2 T Y →
        ∀ v₂ : W, v₂ ≠ 1 →
          Nat.card ↥(MulAction.stabilizer (MulAut W) v₂ ⊓ L) = 240 →
          ∀ A : Subgroup (MulAut W), A ≤ T → IsElemAbelian2 A → Nat.card A = 16 →
            ∃ l ∈ L, l v₂ ∈ commSub
              (⨆ (a : MulAut W) (_ : a ∈ A) (_ : a ≠ 1),
                fixV (Subgroup.zpowers a)) A

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
