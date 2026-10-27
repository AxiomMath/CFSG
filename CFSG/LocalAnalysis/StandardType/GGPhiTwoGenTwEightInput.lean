module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenInput

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def PhiTwoTwE6Eight :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = 64 → (∀ c, σ c = c ^ 8) →
    ∀ (v : WeylGroup TwistTag.E6.tag) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)), ExcIsLongest TwistTag.E6.tag v →
      (∀ c, Fr c = c ^ 8) → g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
      (⨆ γ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ},
        phiTwoCompIn (twistedE6RootGroup K σ) g0 γ.1) = ⊤

@[expose] def PhiTwoTwE6GenInputNeThree :
    Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (n : ℕ), 2 ≤ n → n ≠ 3 →
    Nat.card K = (2 ^ n) ^ 2 → (∀ c, σ c = c ^ 2 ^ n) → ∀ (v : WeylGroup TwistTag.E6.tag)
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)), ExcIsLongest TwistTag.E6.tag v →
      (∀ c, Fr c = c ^ 2 ^ n) → g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) →
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
      (⨆ γ : {γ : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag γ},
        phiTwoCompIn (twistedE6RootGroup K σ) g0 γ.1) = ⊤

theorem phiTwoTwE6GenInput_of_eight (h8 : PhiTwoTwE6Eight) (hne : PhiTwoTwE6GenInputNeThree) :
    PhiTwoTwE6GenInput := by
  intro K _ _ σ n hn hcard hσ v Fr g0 hv hFr hg0C hg0
  by_cases h3 : n = 3
  · subst h3
    exact h8 K σ (by simpa using hcard) (by simpa using hσ) v Fr g0 hv (by simpa using hFr) hg0C
      hg0
  · exact hne K σ n hn h3 hcard hσ v Fr g0 hv hFr hg0C hg0

end CFSG.StandardType

end
