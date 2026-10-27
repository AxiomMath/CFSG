module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTwE6TriD4RankKnown : Prop :=
  ∀ m : ℕ, LargeEvenInLambda2 (⟨.twE6, 0, m⟩ : LargeEvenLabel) → 3 ∣ 2 ^ m + 1 →
    LargeEvenLabelAll (⟨.twE6, 0, m⟩ : LargeEvenLabel) fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ 3 = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
            GGHasLabel (⟨.triD4, 0, m⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) →
              ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A → e ∈ A →
                (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → Nat.card A ≤ 3 ^ 4

end CFSG.StandardType

end
