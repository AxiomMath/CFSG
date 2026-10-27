module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenKG
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator

structure TwE6ThreeFrame
    {n : ℕ} {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {L' : Type} [Group L'] (ψ₀ : L' →* ↥(twistedE6RootGroup K σ))
    (A : Subgroup (MulAut L')) where
  ζ : (AlgebraicClosure K)ˣ
  hζ : ζ ^ 3 = 1
  hζo : orderOf ζ = 3
  E : Subgroup (twistedE6RootGroup K σ)
  F : TwE6Frame K σ n 3 E
  κ : ↥A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)
  t : (Fin Tag.E6.rank → ZMod 3) → ModGL TwistTag.E6.tag K
  T : Subgroup L'
  hv : ExcIsLongest TwistTag.E6.tag F.v
  hκinj : Function.Injective κ
  hκrange : κ.range = ⊤ ∨ ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ NoOffRest.hypE6
  htF : ∀ x, baseChangeGL (algebraMap K (AlgebraicClosure K)) (t x) =
    F.g0 * rootDiagUnit TwistTag.E6.tag (TableBExc.E6Three.zetaVec ζ hζ x) * F.g0⁻¹
  hconj : ∀ (a : ↥A) (l : L'),
    ((ψ₀ ((a : MulAut L') l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
      t (Multiplicative.toAdd (κ a)) *
        ((ψ₀ l : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
          (t (Multiplicative.toAdd (κ a)))⁻¹
  hTodd : ∀ z ∈ ψ₀.ker, Odd (orderOf z) → z ∈ T
  hTfix : ∀ a ∈ A, ∀ y ∈ T, a y = y
  hHyp : ∀ x ∈ NoOffRest.hypE6, ∃ y ∈ T, y ^ 3 = 1 ∧ ∃ b : ↥A,
    MulAut.conj y = (b : MulAut L') ∧ Multiplicative.toAdd (κ b) = x
  hnorm : ∀ m : L', MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) →
    ∃ u : WeylGroup .E6, ∀ a b : ↥A,
      (b : MulAut L') = MulAut.conj m * a * (MulAut.conj m)⁻¹ →
        Multiplicative.toAdd (κ b) = adAct .E6 3 u (Multiplicative.toAdd (κ a))

theorem ggTwE6Three_frame_exists
    {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range, ∀ l, φ (ψ₀ l) = ψ₀ (a l))
    (h5 : 3 ^ 5 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A) :
    Nonempty (TwE6ThreeFrame (n := n) σ ψ₀ A) := by
  classical
  have hn1 : 1 ≤ n := by omega
  obtain ⟨ζ, Fr, hζ, hζo, hFr⟩ := exists_zeta_frobenius_twE6Three hK
  obtain ⟨g, κ, t, T, hg, hglang, hκinj, hκrange, ht, hconj, hTodd, hTfix, hHyp, hnorm⟩ :=
    TwE6ThreeRootGen.exists_frame_torus (L' := L') (ψ₀ := ψ₀) (A := A) (Fr := Fr)
      (ζ := ζ) hn1 hK σ hσ h3 hFr hζ hζo hψ₀ hker hperf hA hAH h5 hsc
  obtain ⟨E, F, -, hFv, hFg⟩ :=
    TwE6ThreeRootGen.exists_twE6Frame (K := K) (σ := σ) (n := n) (p := 3) (Fr := Fr)
      (v := CFSG.HardMathSupport.Lang.E6Descent.twE6W0) (g₀ := g) hFr hg hglang
  have hv : ExcIsLongest TwistTag.E6.tag F.v := by
    rw [hFv]
    exact TwE6ThreeRootGen.excIsLongest_twE6W0
  exact ⟨⟨ζ, hζ, hζo, E, F, κ, t, T, hv, hκinj, hκrange, baseChange_twE6Three hζ ht hFg, hconj,
    hTodd, hTfix, hHyp, hnorm⟩⟩

end CFSG.StandardType

end
