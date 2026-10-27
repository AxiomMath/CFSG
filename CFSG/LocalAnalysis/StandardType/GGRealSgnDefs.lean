module

public import CFSG.LocalAnalysis.StandardType.GGRealKGTorusComponentsDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGKGConjCommAt {R : Type} [Group R] (E : Subgroup R) (w₀ : R) : Prop :=
  ∀ u ∈ Subgroup.normalizer (E : Set R), ∀ e ∈ E,
    (u * w₀ * u⁻¹) * (w₀ * e * w₀⁻¹) * (u * w₀ * u⁻¹)⁻¹ =
      w₀ * ((u * w₀ * u⁻¹) * e * (u * w₀ * u⁻¹)⁻¹) * w₀⁻¹

@[expose] def GGKGSgnComponentDatumAt (p : ℕ) {R : Type} [Group R] (E : Subgroup R) : Prop :=
  ∀ w₀ : R, GGKGIsReflAt p E w₀ → GGKGConjCommAt E w₀ →
    ∃ w : R, (∀ e ∈ E, w * e * w⁻¹ = w₀ * e * w₀⁻¹) ∧ ∃ J : Subgroup R, w ∈ J ∧
      IsComponentOf J
        (Subgroup.centralizer ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R)) ∧
      p ∣ Nat.card J

@[expose] def GGKGSgnComponentDatum (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E → p ^ r ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → GGKGSgnComponentDatumAt p E

@[expose] def GGTorusSgnComponents (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      ∀ φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A, GGIsReflection p φ →
        (∀ (u : L') (hu : MulAut.conj u ∈ Subgroup.normalizer (A : Set (MulAut L'))),
          GGTorusWeylElt p A u → Commute (ggConjAut A hu * φ * (ggConjAut A hu)⁻¹) φ) →
        ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
          (J : Subgroup L'), GGTorusWeylElt p A n ∧ ggConjAut A hn = φ ∧ n ∈ J ∧
          IsComponentOf J (ggHypCent A n) ∧ p ∣ Nat.card J

@[expose] def GGRealSgnOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
    LargeEvenLabelAll lab fun R _ I _ => GGTorusSgnComponents p 0 R I

end CFSG.StandardType

end
