module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGTorusReflBridge (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ∀ (β : MulAut L') (β' : MulAut R), (∀ l : L', β' (ψ l) = ψ (β l)) →
        (∀ a ∈ A, β * a * β⁻¹ ∈ A) →
        (∀ a ∈ A, β ^ (p - 1) * a * (β ^ (p - 1))⁻¹ = a) →
        Nat.card {a : A // β * (a : MulAut L') * β⁻¹ = a} * p = Nat.card A →
        ∃ n : L', (∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧
            ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
          ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ = β * a * β⁻¹

theorem ggTorusReflBridge_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    {I : Set (MulAut R)} {I' : Set (MulAut R')} (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGTorusReflBridge p r R' I') : GGTorusReflBridge p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 β β' hββ' hN hpow hfix
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3 β
    (MulAut.congr e β') ?_ hN hpow hfix
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφI, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφI, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]
  · intro l
    simp [MulAut.congr_apply, hββ' l]

end CFSG.StandardType

end
