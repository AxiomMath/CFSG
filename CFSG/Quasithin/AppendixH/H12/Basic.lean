module

public import CFSG.Milestones.ASVolI.H6
public import CFSG.Quasithin.AppendixH.H12.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH

@[expose] def FormClause {G : Type*} [Group G] {V : Type*} [CommGroup V] {K : Type*} [Field K]
    (ρ : G →* MulAut V) (L : Subgroup G) (ι : K →+* AddMonoid.End (Additive V))
    (f : V → V → K) : Prop :=
  IsUnitaryForm ι f ∧
    (∀ g ∈ L, (∀ (c : K) (v : V), ρ g (kSmul ι c v) = kSmul ι c (ρ g v)) ∧
      ∀ u v : V, f (ρ g u) (ρ g v) = f u v) ∧
    (∃ q : V → ZMod 2, IsQuadFormOn q ∧ (∀ u : V, f u u = 0 ∨ f u u = 1) ∧
      (∀ u : V, q u = 0 ↔ f u u = 0) ∧ ∀ g ∈ L, ∀ u : V, q (ρ g u) = q u)

@[expose] def Clause4 {G : Type*} [Group G] (L T M N : Subgroup G) : Prop :=
  IsMaximalIn M L ∧ IsMaximalIn N L ∧ T ≤ M ∧ T ≤ N ∧ M ≠ N ∧
    (∀ X : Subgroup G, IsMaximalIn X L → T ≤ X → X = M ∨ X = N) ∧
    (IsElemAbelian 2 (pCoreOf 2 M) ∧ Nat.card ↥(pCoreOf 2 M) = 16 ∧
      IsExtHatOf M (pCoreOf 2 M) ↥(alternatingGroup (Fin 6))) ∧
    (∃ X : Subgroup G, IsIntDirect N X ((Subgroup.center ↥L).map L.subtype) ∧
      IsElemAbelian 2 (pCoreOf 2 X) ∧ Nat.card ↥(pCoreOf 2 X) = 16 ∧
      IsExtOf X (pCoreOf 2 X) (Equiv.Perm (Fin 5)))

@[expose] def Clause5 {G : Type*} [Group G] {V : Type*} [CommGroup V] {K : Type*} [Field K]
    (ρ : G →* MulAut V) (L T N : Subgroup G) (ι : K →+* AddMonoid.End (Additive V))
    (f : V → V → K) (V₁ : Subgroup V) : Prop :=
  IsIsoPoint ι f V₁ ∧ (∀ t ∈ T, ∀ x ∈ V₁, ρ t x ∈ V₁) ∧
    (∀ P : Subgroup V, IsIsoPoint ι f P → (∀ t ∈ T, ∀ x ∈ P, ρ t x ∈ P) → P = V₁) ∧
    ptStab ρ L V₁ = N

@[expose] def Clause6 {G : Type*} [Group G] {V : Type*} [CommGroup V] {K : Type*} [Field K]
    (ρ : G →* MulAut V) (L M : Subgroup G) (f : V → V → K) : Prop :=
  fixV ((pCoreOf 2 M).map ρ) = commV ((pCoreOf 2 M).map ρ) ∧
    (∀ u ∈ fixV ((pCoreOf 2 M).map ρ), ∀ v ∈ fixV ((pCoreOf 2 M).map ρ), f u v = 0) ∧
    Nat.card ↥(fixV ((pCoreOf 2 M).map ρ)) = 4 ^ 3 ∧
    cenIn ρ L (fixV ((pCoreOf 2 M).map ρ)) = pCoreOf 2 M

@[expose] def Clause78 {G : Type*} [Group G] {V : Type*} [CommGroup V] {K : Type*} [Field K]
    (ρ : G →* MulAut V) (L M : Subgroup G) (ι : K →+* AddMonoid.End (Additive V))
    (f : V → V → K) (V₁ V₂ : Subgroup V) : Prop :=
  IsIsoPoint ι f V₂ ∧ V₁ ≤ fixV ((pCoreOf 2 M).map ρ) ∧
    V₂ ≤ fixV ((pCoreOf 2 M).map ρ) ∧ V₁ ≠ V₂ ∧
    (∀ P : Subgroup V, IsIsoPoint ι f P → P ≤ fixV ((pCoreOf 2 M).map ρ) →
      IsConjPt ρ M P V₁ ∨ IsConjPt ρ M P V₂) ∧
    ¬ IsConjPt ρ M V₁ V₂ ∧
    ptStab ρ M V₂ = ptStab ρ L V₂ ∧
    (∃ X : Subgroup G, IsIntDirect (ptStab ρ L V₂) X ((Subgroup.center ↥L).map L.subtype) ∧
      IsElemAbelian 2 (pCoreOf 2 X) ∧ Nat.card ↥(pCoreOf 2 X) = 16 ∧
      IsExtOf X (pCoreOf 2 X) ↥(alternatingGroup (Fin 5))) ∧
    (∀ P : Subgroup V, IsIsoPoint ι f P → IsConjPt ρ L P V₁ ∨ IsConjPt ρ L P V₂) ∧
    ¬ IsConjPt ρ L V₁ V₂ ∧
    (∃ t ∈ pCoreOf 2 M, orderOf t = 2 ∧ commV (Subgroup.zpowers (ρ t)) = V₁ ⊔ V₂)

@[expose] def H12Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G),
    IsHat ↥L ↥CFSG.Blueprint.NativeSporadic.M22 → CFSG.generalizedFitting G = L →
    ((∃ (V₀ : Type) (_ : CommGroup V₀) (ρ₀ : ↥L →* MulAut V₀), IsFaithIrr12 ρ₀) ∧
      ∀ (V₁ V₂ : Type) [CommGroup V₁] [CommGroup V₂] (ρ₁ : ↥L →* MulAut V₁) (ρ₂ : ↥L →* MulAut V₂),
        IsFaithIrr12 ρ₁ → IsFaithIrr12 ρ₂ → ModIso ρ₁ ρ₂) ∧
    ∀ (V : Type) [CommGroup V] (ρ : G →* MulAut V), IsFaithIrr12 (ρ.comp L.subtype) →
      ∃ (K : Type) (_ : Field K), Nat.card K = 4 ∧
        ∃ (ι : K →+* AddMonoid.End (Additive V)) (f : V → V → K),
          IsUnitaryForm ι f ∧
          (∀ g ∈ L, (∀ (c : K) (v : V), ρ g (kSmul ι c v) = kSmul ι c (ρ g v)) ∧
            ∀ u v : V, f (ρ g u) (ρ g v) = f u v) ∧
          (∃ q : V → ZMod 2, IsQuadFormOn q ∧ (∀ u : V, f u u = 0 ∨ f u u = 1) ∧
            (∀ u : V, q u = 0 ↔ f u u = 0) ∧ ∀ g ∈ L, ∀ u : V, q (ρ g u) = q u) ∧
          (∀ (U : Type) [CommGroup U] (σ : G →* MulAut U), (∀ u : U, u ^ 2 = 1) →
            Function.Injective σ → IsIrredOn σ.range ⊤ →
            (∃ t : G, orderOf t = 2 ∧ rk ↥(commV (Subgroup.zpowers (σ t))) ≤ 4) →
              ModIso (σ.comp L.subtype) (ρ.comp L.subtype)) ∧
          (∀ T : Subgroup G, IsSylowIn 2 T L → ∃ M N : Subgroup G,
            (IsMaximalIn M L ∧ IsMaximalIn N L ∧ T ≤ M ∧ T ≤ N ∧ M ≠ N ∧
              (∀ X : Subgroup G, IsMaximalIn X L → T ≤ X → X = M ∨ X = N) ∧
              (IsElemAbelian 2 (pCoreOf 2 M) ∧ Nat.card ↥(pCoreOf 2 M) = 16 ∧
                IsExtHatOf M (pCoreOf 2 M) ↥(alternatingGroup (Fin 6))) ∧
              (∃ X : Subgroup G, IsIntDirect N X ((Subgroup.center ↥L).map L.subtype) ∧
                IsElemAbelian 2 (pCoreOf 2 X) ∧ Nat.card ↥(pCoreOf 2 X) = 16 ∧
                IsExtOf X (pCoreOf 2 X) (Equiv.Perm (Fin 5)))) ∧
            ∃ V₁ : Subgroup V, IsIsoPoint ι f V₁ ∧ (∀ t ∈ T, ∀ x ∈ V₁, ρ t x ∈ V₁) ∧
              (∀ P : Subgroup V, IsIsoPoint ι f P → (∀ t ∈ T, ∀ x ∈ P, ρ t x ∈ P) → P = V₁) ∧
              ptStab ρ L V₁ = N ∧
              (fixV ((pCoreOf 2 M).map ρ) = commV ((pCoreOf 2 M).map ρ) ∧
                (∀ u ∈ fixV ((pCoreOf 2 M).map ρ), ∀ v ∈ fixV ((pCoreOf 2 M).map ρ), f u v = 0) ∧
                Nat.card ↥(fixV ((pCoreOf 2 M).map ρ)) = 4 ^ 3 ∧
                cenIn ρ L (fixV ((pCoreOf 2 M).map ρ)) = pCoreOf 2 M) ∧
              ∃ V₂ : Subgroup V, IsIsoPoint ι f V₂ ∧ V₁ ≤ fixV ((pCoreOf 2 M).map ρ) ∧
                V₂ ≤ fixV ((pCoreOf 2 M).map ρ) ∧ V₁ ≠ V₂ ∧
                (∀ P : Subgroup V, IsIsoPoint ι f P → P ≤ fixV ((pCoreOf 2 M).map ρ) →
                  IsConjPt ρ M P V₁ ∨ IsConjPt ρ M P V₂) ∧
                ¬ IsConjPt ρ M V₁ V₂ ∧
                ptStab ρ M V₂ = ptStab ρ L V₂ ∧
                (∃ X : Subgroup G, IsIntDirect (ptStab ρ L V₂) X ((Subgroup.center ↥L).map L.subtype) ∧
                  IsElemAbelian 2 (pCoreOf 2 X) ∧ Nat.card ↥(pCoreOf 2 X) = 16 ∧
                  IsExtOf X (pCoreOf 2 X) ↥(alternatingGroup (Fin 5))) ∧
                (∀ P : Subgroup V, IsIsoPoint ι f P → IsConjPt ρ L P V₁ ∨ IsConjPt ρ L P V₂) ∧
                ¬ IsConjPt ρ L V₁ V₂ ∧
                (∃ t ∈ pCoreOf 2 M, orderOf t = 2 ∧ commV (Subgroup.zpowers (ρ t)) = V₁ ⊔ V₂) ∧
                (∀ TG : Subgroup G, IsSylowIn 2 TG ⊤ → T ≤ TG →
                  fixV (TG.map ρ) = V₁ ⊓ fixV (TG.map ρ) ∧
                  (L < ⊤ → rk ↥(fixV (TG.map ρ)) = 1))) ∧
          (E3.mParam ρ.range = 4 ∧ H.betaH ρ.range = 8 ∧ ¬ H.IsFOneModule ρ.range ∧
            CFSG.Open.pRank 2 (⊤ : Subgroup G) ≤ 5)

end CFSG.Quasithin.AppendixH.H12
