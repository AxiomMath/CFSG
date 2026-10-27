module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6Base
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTUnits

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.LieType.Universal CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus


@[expose] def TwE6BigGroup {X : Type} [Group X] [Finite X] (n f p : ℕ) (ψ : (ggU .twistedE6 n f).K →* X)
    (G₀ B₁ A : Subgroup X) : Prop :=
  B₁ ≤ A ∧ IsElemAbelian p A ∧ A ≤ Subgroup.normalizer (G₀ : Set X) ∧
    (∀ a ∈ A, GGPsiInnerDiag (ggU .twistedE6 n f).D ψ a) ∧
    A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥ ∧
    (∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A) ∧
    p ^ LargeEvenTwoLocalRank p ↥(A ⊔ G₀) ≤ Nat.card A

@[expose] def TwE6RankFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ 3 G₀ B₁ D J L x →
    9 ∣ 2 ^ f + 1 → ∀ A : Subgroup X, TwE6BigGroup n f 3 ψ G₀ B₁ A → 3 ^ 5 ≤ Nat.card A

structure TwE6BaseCompat {X : Type} [Group X] (n f p : ℕ) (ψ : (ggU .twistedE6 n f).K →* X)
    {G₀ B₁ D J : Subgroup X} {x : X} (B : ExcBase .E6 f p G₀ B₁ D J x) : Prop where
  Φ_eq : B.Δ.Φ = ggPhi .twistedE6 f
  η_psi : ∀ (k : (ggU .twistedE6 n f).K) (h : ψ k ∈ G₀),
    @Eq (ModGL (langTag .twistedE6) GGL) (B.η ⟨ψ k, h⟩)
      ((@id (ModGL (langTag .twistedE6) GGL) B.Δ.g0)⁻¹ * ggIotaK .twistedE6 n f B.one_le_f k *
        (@id (ModGL (langTag .twistedE6) GGL) B.Δ.g0))
  law : ∃ (ht : GGExcFive .twistedE6) (w : WeylGroup (langTag .twistedE6)),
    GGWeylLaw .twistedE6 p f ht w ∧
      B.Δ.n = canonicalRep (coxeterSystem (langTag .twistedE6)) GGL w

@[expose] def TwE6Frame : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1 ∧ ¬ 9 ∣ 2 ^ f + 1) →
    ∃ B : ExcBase .E6 f p G₀ B₁ D J x, TwE6BaseCompat n f p ψ B

@[expose] def TwE6PairSel : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .twistedE6 n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixPosHyp .twistedE6 n f ψ p G₀ B₁ D J L x →
    ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1 ∧ ¬ 9 ∣ 2 ^ f + 1) →
    ∀ B : ExcBase .E6 f p G₀ B₁ D J x, TwE6BaseCompat n f p ψ B →
    ∃ R Rm : Subgroup X, R ≤ J ∧ Rm ≤ J ∧ GGRootPosG0 .twistedE6 n f p ψ R Rm ∧
      Nonempty (ExcPairData B R Rm)

theorem excU1b_of_frame_pair (hF : TwE6Frame) (hP : TwE6PairSel) : ExcU1b := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos hres
  obtain ⟨B, hB⟩ := hF X n f ψ p G₀ B₁ D J L x hpos hres
  obtain ⟨R, Rm, hRJ, hRmJ, hG, ⟨Pd⟩⟩ := hP X n f ψ p G₀ B₁ D J L x hpos hres B hB
  exact ⟨R, Rm, hRJ, hRmJ, hG, ⟨ExcPacket.ofBasePair B Pd⟩⟩

end CFSG.StandardType.LieKnownR2.ExcPos
