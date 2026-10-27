module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLIDProof

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGTableBModuleSCr (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ (H : Subgroup (MulAut L')) (W : Set L'), H ≤ A ∧ H ≠ ⊥ ∧ Nat.card A ≤ p * Nat.card H ∧
        (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
          ∀ h ∈ H, MulAut.conj n * h * (MulAut.conj n)⁻¹ ∈ H) ∧
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ∀ A' : Subgroup (MulAut L'), A' ≤ A → A' ≠ ⊥ →
          (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → H ≤ A'

theorem ggTableBModuleSCr_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') {I : Set (MulAut R)} {I' : Set (MulAut R')}
    (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I') (h : GGTableBModuleSCr p r R' I') :
    GGTableBModuleSCr p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf A hA ?_ hr h3 hsc
  · intro l hl
    exact hker (by simpa [MonoidHom.mem_ker] using hl)
  · intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, hI φ hφ, fun l => ?_⟩
    simp [MulAut.congr_apply, hφa l]

end CFSG.StandardType

namespace CFSG.StandardType.LinUnitL

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA TypeANbrDvd

variable {d p : ℕ} {K : Type} [Field K]

section Scalar

variable {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}

theorem ActsDiag.mul_const [CharP K 2] {a : MulAut L'} {t : Fin d → K} (ha : ActsDiag φ' a t)
    {c : K} (hc : c ≠ 0) : ActsDiag φ' a (fun k => t k * c) := by
  obtain ⟨D, hD, haD⟩ := ha
  refine ⟨D * Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc), ?_, fun s => ?_⟩
  · rw [Units.val_mul, hD, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_mul_diagonal]
    rfl
  · rw [haD, map_mul, MulAut.mul_apply, CatalogueBHigherLinearAction.slConjugation_scalar,
      MulAut.one_apply]

end Scalar

end CFSG.StandardType.LinUnitL

end
