module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

@[expose] def GammaL2 (K : Type) [Field K] : Subgroup (Equiv.Perm (Fin 2 → K)) :=
  Subgroup.closure ({f | ∃ A : GL (Fin 2) K, ∀ v, f v = (A : Matrix (Fin 2) (Fin 2) K).mulVec v} ∪
    {f | ∃ σ : K ≃+* K, ∀ v, f v = σ ∘ v})

@[expose] def Stmt5_2_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ) (M2 : Subgroup G)
    (π : ↥M2 →* Equiv.Perm (Fin 7)), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfTypeM23 M L H B D T → IsM23Setting T H M2 π →
      ∀ X : Subgroup G, CFSG.Quasithin.IsSylowIn 3 X (M ⊓ centralizerModO2 L) →
        Subgroup.normalizer (X : Set G) ≤ M ∧
        ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 4 ∧
          Nonempty (↥(M ⊓ Subgroup.normalizer (X : Set G)) ≃* ↥(GammaL2 K))

end CFSG.Quasithin.H13
