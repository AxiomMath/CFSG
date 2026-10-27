module

public import CFSG.LocalAnalysis.StandardType.GGR4PumpTwKnownDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGPumpTwLabConcl (lab : LargeEvenLabel) (f : ℕ) : Prop :=
  lab.n = f ∧
    ((∃ k : ℕ, 1 ≤ k ∧
        ((lab = ⟨.A, 5 + 2 * k, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨
          (lab = ⟨.twA, 5 + 2 * k, f⟩ ∧ 3 ∣ 2 ^ f - 1) ∨
          (lab = ⟨.twD, 4 + k, f⟩ ∧ (3 ∣ 2 ^ f - 1 ∨ (3 ∣ 2 ^ f + 1 ∧ Even k))) ∨
          (lab = ⟨.D, 4 + k, f⟩ ∧ 3 ∣ 2 ^ f + 1 ∧ Odd k))) ∨
      (lab = ⟨.E6, 0, f⟩ ∧ 3 ∣ 2 ^ f + 1) ∨ (lab = ⟨.twE6, 0, f⟩ ∧ 3 ∣ 2 ^ f - 1))

@[expose] def GGPumpTwLabAt (lab : LargeEvenLabel) : Prop :=
  LargeEvenLabelAll lab fun R _ I _ =>
    ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ (e : MulAut L') (J : Subgroup L') (f : ℕ), e ≠ 1 → e ^ 3 = 1 →
        (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) → CFSG.Assembly.IsComponentOf J (ggFixSub e) →
        GGPumpTwJLab f (J ⧸ Subgroup.center J) → GGPumpTwLabConcl lab f

@[expose] def GGPumpTwLabRAKnown : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    ((lab.tag = .A ∧ 3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
      (lab.tag = .twA ∧ 3 ∣ lab.rank + 1 ∧ 3 ∣ 2 ^ lab.n + 1)) → GGPumpTwLabAt lab

end CFSG.StandardType

end
