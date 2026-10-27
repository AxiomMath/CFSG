module

public import CFSG.LocalAnalysis.StandardType.GGKGADefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace KGA

@[expose] def GGF4CentAt (p f : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R),
    Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ e a : MulAut L', e ^ p = 1 → e ≠ 1 → e * a = a * e →
      (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      ∀ J : Subgroup L', IsComponentOf J (ggFixSub e) →
        GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J) →
        (∀ x ∈ J, a x ∈ J) ∧ ∃ j ∈ J, ∀ x ∈ J, a x = j * x * j⁻¹

@[expose] def GGF4C3CentInputStrong : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f : ℕ, 1 ≤ f →
    LargeEvenLabelAll ⟨.F4, 4, f⟩ fun R _ I _ => GGF4CentAt p f R I

@[expose] def GGF4AutOrderAt (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 4 ≤ Nat.card E →
    Nat.card E = p ^ 4 ∧ Nat.card (ggAutomizer ⊤ E) = 1152

end KGA

end CFSG.StandardType

end
