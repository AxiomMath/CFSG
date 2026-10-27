module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwCent
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcNorm
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwNorm2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KE
  CFSG.LieType.AlgebraicGroups

section AtFrame


theorem ggKGTwE6_normalizer_weyl
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (hp : p.Prime) (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E)
    (hv : (p ∣ 2 ^ n - 1 ∧ F.v = 1) ∨ (p ∣ 2 ^ n + 1 ∧ ExcIsLongest TwistTag.E6.tag F.v))
    {x : twistedE6RootGroup K σ} (hx : x ∈ Subgroup.normalizer (E : Set (twistedE6RootGroup K σ))) :
    ∃ u : WeylGroup TwistTag.E6.tag,
      (p ∣ 2 ^ n - 1 → ∀ w₀ : WeylGroup TwistTag.E6.tag, ExcIsLongest TwistTag.E6.tag w₀ →
        u * w₀ = w₀ * u) ∧
      ∀ e ∈ E,
        F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((x * e * x⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0 =
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u *
            (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0) *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹ := by
  exact ggKGTn_normalizer_weyl hK hσ hp hp5 F hv hx

theorem ggKGTwE6_normalizer_faithful
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {n : ℕ} {p : ℕ}
    {E : Subgroup (twistedE6RootGroup K σ)}
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime) (hp5 : 5 ≤ p) (F : TwE6Frame K σ n p E)
    (hv : (p ∣ 2 ^ n - 1 ∧ F.v = 1) ∨ (p ∣ 2 ^ n + 1 ∧ ExcIsLongest TwistTag.E6.tag F.v))
    {u : WeylGroup TwistTag.E6.tag}
    (hu : ∀ e ∈ E,
      canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u *
          (F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)⁻¹ =
      F.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((e : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * F.g0) :
    u = 1 := by
  exact ggKGTn_normalizer_faithful hK hσ hp hp5 F hv hu

end AtFrame

end CFSG.StandardType
