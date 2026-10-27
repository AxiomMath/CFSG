module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpTwNotFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

open scoped Pointwise

@[expose] def GGPumpTwJLab (f : ℕ) (Y : Type) [Group Y] : Prop :=
  (3 ∣ 2 ^ f - 1 ∧ GGHasLabel ⟨.twA, 5, f⟩ Y) ∨ (3 ∣ 2 ^ f + 1 ∧ GGHasLabel ⟨.A, 5, f⟩ Y) ∨
    GGHasLabel ⟨.twD, 4, f⟩ Y

@[expose] def GGPumpTwLabelKnown : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ =>
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (e : MulAut L') (J : Subgroup L') (f : ℕ), e ≠ 1 → e ^ 3 = 1 →
          (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) → CFSG.Assembly.IsComponentOf J (ggFixSub e) →
          GGPumpTwJLab f (J ⧸ Subgroup.center J) →
          lab.n = f ∧
            ((∃ k : ℕ, 1 ≤ k ∧
                ((lab = ⟨.A, 5 + 2 * k, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨
                  (lab = ⟨.twA, 5 + 2 * k, f⟩ ∧ 3 ∣ 2 ^ f - 1) ∨
                  (lab = ⟨.twD, 4 + k, f⟩ ∧ (3 ∣ 2 ^ f - 1 ∨ (3 ∣ 2 ^ f + 1 ∧ Even k))) ∨
                  (lab = ⟨.D, 4 + k, f⟩ ∧ 3 ∣ 2 ^ f + 1 ∧ Odd k))) ∨
              (lab = ⟨.E6, 0, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨ (lab = ⟨.twE6, 0, f⟩ ∧ 3 ∣ 2 ^ f - 1))

@[expose] def GGPumpTwExcKnown : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∀ lab : LargeEvenLabel,
    ((lab = ⟨.E6, 0, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨ (lab = ⟨.twE6, 0, f⟩ ∧ 3 ∣ 2 ^ f - 1)) →
    LargeEvenLabelAll lab fun R _ I _ =>
      GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
          ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
          ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
            (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
            3 ^ 4 ≤ Nat.card A → GGTorusSelfCent 3 A →
            Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = 1152

end CFSG.StandardType

end
