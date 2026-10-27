module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSU6NoParabolicAt3 {R : Type} [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
      GGRankOneSetup I ψ 3 e J 3 a →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → Nat.card A = 3 ^ 3 → e ∈ A → a ∈ A →
        (∀ c ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (c l)) →
        (∀ c ∈ A, ∀ j ∈ J, c j ∈ J) →
        ∀ V : Subgroup (MulAut R), V ≠ ⊥ → IsPGroup 2 V → V ≤ Subgroup.closure I →
          ¬ ∀ c ∈ A, ∀ φ : MulAut R, (∀ l : L', φ (ψ l) = ψ (c l)) →
              ∀ v ∈ V, φ * v * φ⁻¹ ∈ V

end CFSG.StandardType

end
