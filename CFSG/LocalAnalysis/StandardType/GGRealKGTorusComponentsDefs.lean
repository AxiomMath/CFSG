module

public import CFSG.LocalAnalysis.StandardType.GGKGForkTransfer

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTorusComponents (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ →
        ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
          (J : Subgroup L'), GGTorusWeylElt p A n ∧ ggConjAut A hn = φ ∧ n ∈ J ∧
          IsComponentOf J (ggHypCent A n) ∧ p ∣ Nat.card J

theorem ggTorusComponents_of_rootSL2 {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusRootSL2 p r R I) : GGTorusComponents p r R I := by
  intro L' _ _ ψ A hTB φ hφauto hφrefl
  obtain ⟨n, hn, J, hW, hnφ, hnJ, hcomp, hpJ, -⟩ := h L' ψ A hTB φ hφauto hφrefl
  exact ⟨n, hn, J, hW, hnφ, hnJ, hcomp, hpJ⟩

@[expose] def GGKGComponentDatumAt (p : ℕ) {R : Type} [Group R] (E : Subgroup R) : Prop :=
  ∀ w₀ : R, GGKGIsReflAt p E w₀ →
    ∃ w : R, (∀ e ∈ E, w * e * w⁻¹ = w₀ * e * w₀⁻¹) ∧ ∃ J : Subgroup R, w ∈ J ∧
      IsComponentOf J
        (Subgroup.centralizer ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R)) ∧
      p ∣ Nat.card J

@[expose] def GGKGComponentDatum (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E → p ^ r ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → GGKGComponentDatumAt p E

@[expose] def GGCentrallyClosed (R : Type) [Group R] : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Function.Injective ψ

end CFSG.StandardType

end
