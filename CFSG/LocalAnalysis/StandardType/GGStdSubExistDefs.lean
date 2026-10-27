module

public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGAdmissible (p : ℕ) (L' : Type) [Group L'] (A : Subgroup (MulAut L')) : Prop :=
  (∃ U : Subgroup (MulAut L'), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set (MulAut L'))) ∨
    ((∃ a ∈ A, a ∉ (MulAut.conj : L' →* MulAut L').range) ∧
      ∀ E : Subgroup L', IsElemAbelian p E → Nat.card E ≤ Nat.card A) ∨
    (p ∣ Nat.card (Subgroup.center L') ∧
      ∀ E : Subgroup L', IsElemAbelian p E → Nat.card E ≤ p * Nat.card A)

@[expose] def GGEndNodeAdm (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGAdmissible p L' A →
      ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
        ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)

theorem ggEndNodeAdm_of_ggEndNode {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGEndNode p r R I) : GGEndNodeAdm p r R I :=
  fun L' _ _ ψ hψ hker hL A hA hAI hr h3 _ => h L' ψ hψ hker hL A hA hAI hr h3

@[expose] def GGBstarBoundInn (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A Ah : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      (∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a u ∈ U) →
      A ≤ Ah → IsElemAbelian p Ah → p ^ 2 * Nat.card A ≤ Nat.card Ah →
      ∃ A' : Subgroup (MulAut L'), A < A' ∧ A' ≤ Ah ∧
        ∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A', ∀ u ∈ U, a u ∈ U

@[expose] def GGInnLocalInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L : Subgroup G),
    GGThmIHyp p B x L → ∃ U : Subgroup G, U ≤ L ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧
      B ≤ Subgroup.normalizer (U : Set G)

end CFSG.StandardType
