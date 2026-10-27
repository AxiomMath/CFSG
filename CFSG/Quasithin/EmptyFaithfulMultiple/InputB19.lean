module

public import CFSG.Quasithin.Background.B1Basic
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Vocabulary

variable {Γ : Type*} [Group Γ]

@[expose] def IsInnerDirectProduct {ι : Type*} (H : ι → Subgroup Γ) (K : Subgroup Γ) : Prop :=
  (∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a) ∧ iSupIndep H ∧ ⨆ i, H i = K

@[expose] def fittingOfSub (X : Subgroup Γ) : Subgroup Γ :=
  (CFSG.fittingSubgroup ↥X).map X.subtype

@[expose] def oddCoreOfSub (X : Subgroup Γ) : Subgroup Γ :=
  (CFSG.oddCore ↥X).map X.subtype

end Vocabulary

@[expose] def InputB19 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ X : Subgroup (MulAut V), pCoreOf 2 X = ⊥ →
      ⁅fittingOfSub X, ffJP {A | IsFFStarMin X A} X⁆ ≠ ⊥ →
      ∃ (s : ℕ) (H : Fin s → Subgroup (MulAut V)),
        (∀ i, H i ≤ X ∧ Nonempty (↥(H i) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) ∧
        IsInnerDirectProduct
          (fun o : Option (Fin s) => o.elim
            (ffJP {A | IsFFStarOffender X A} (X ⊓ Subgroup.centralizer
              ((⁅fittingOfSub X, ffJP {A | IsFFStarMin X A} X⁆ : Subgroup (MulAut V)) :
                Set (MulAut V)))) H)
          (ffJ X) ∧
        IsInnerDirectProduct (fun i => oddCoreOfSub (H i))
          ⁅fittingOfSub X, ffJP {A | IsFFStarMin X A} X⁆ ∧
        (∀ i, Nat.card ↥(oddCoreOfSub (H i)) = 3) ∧
        IsInnerDirectProduct
          ![⁅fittingOfSub X, ffJP {A | IsFFStarMin X A} X⁆,
            fittingOfSub X ⊓ Subgroup.centralizer
              ((ffJP {A | IsFFStarMin X A} X : Subgroup (MulAut V)) : Set (MulAut V))]
          (fittingOfSub X) ∧
        (∀ i, commV (oddCoreOfSub (H i)) = commV (H i) ∧ Nat.card ↥(commV (H i)) = 4) ∧
        iSupIndep (fun i => commV (oddCoreOfSub (H i))) ∧
        ⨆ i, commV (oddCoreOfSub (H i)) = commV ⁅fittingOfSub X, ffJP {A | IsFFStarMin X A} X⁆ ∧
        (∀ A : Subgroup (MulAut V), (IsFFStarMin X A ∧ ⁅fittingOfSub X, A⁆ ≠ ⊥) ↔
          ∃ i, IsSylowTwoOf A (H i)) ∧
        ∀ A K : Subgroup (MulAut V), IsFFStarMin X A → K ≤ X → ⁅K, A⁆ = K →
          K ≤ ffJP {A | IsFFStarMin X A} X ⊓
            Subgroup.centralizer ((fittingOfSub X : Subgroup (MulAut V)) : Set (MulAut V))

end CFSG.Quasithin.EmptyFaithfulMultiple
