module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylCompDefs
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerShape

public section

namespace CFSG.StandardType.UnitSixThreeKG

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD CFSG.Assembly CFSG.StandardType

@[expose] def IsWeyl {L' : Type} [Group L'] (A : Subgroup (MulAut L')) (n : L') : Prop :=
  ∀ a ∈ A, (n * (a n)⁻¹) ^ 3 = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹

@[expose] def PerLineOn {L' : Type} [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  ∀ a₀ ∈ A, a₀ ≠ 1 → GGFixCompCyclic 3 a₀ →
    ∃ n : L', IsWeyl A n ∧ MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀

theorem ggTorusNoLineComp_of_perLine {R : Type} [Group R] {I : Set (MulAut R)}
    (h : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
      ∀ A : Subgroup (MulAut L'), CFSG.Open.IsElemAbelian 3 A →
        (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → 3 ^ 3 ≤ Nat.card A → PerLineOn A) :
    GGTorusNoLineComp 3 0 R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI _hr h3 _hsc
  refine ⟨{n | IsWeyl A n}, fun n hn => hn, fun _ a₀ ha₀ h1 hcyc => ?_⟩
  obtain ⟨n, hn, hmv⟩ := h L' ψ hψ hker hperf A hA hAI h3 a₀ ha₀ h1 hcyc
  exact ⟨n, hn, hmv⟩

@[expose] def ShapeBad {K : Type} [Field K] (τ : Fin 6 → Kˣ) : Prop :=
  (∃ (v₁ v₂ : Kˣ) (S₁ S₂ : Finset (Fin 6)), v₁ ≠ v₂ ∧ (∀ i, i ∈ S₁ ↔ τ i = v₁) ∧
    (∀ i, i ∈ S₂ ↔ τ i = v₂) ∧ S₁.card = 3 ∧ S₂.card = 3) ∨
  (∃ (v₁ v₂ v₃ : Kˣ) (S₁ S₂ S₃ : Finset (Fin 6)), v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃ ∧
    (∀ i, i ∈ S₁ ↔ τ i = v₁) ∧ (∀ i, i ∈ S₂ ↔ τ i = v₂) ∧ (∀ i, i ∈ S₃ ↔ τ i = v₃) ∧
    S₁.card = 2 ∧ S₂.card = 2 ∧ S₃.card = 2)

@[expose] def ShapeBadMat {K : Type} [Field K] {n : ℕ} (hKd : UnitaryFieldData 2 n K)
    (M : GL (Fin 6) K) : Prop :=
  ∃ P ∈ primeFormUnitary hKd (idGram K 6), ∃ τ : Fin 6 → Kˣ,
    P⁻¹ * M * P = diagHom 6 τ ∧ ShapeBad τ

end CFSG.StandardType.UnitSixThreeKG

end
