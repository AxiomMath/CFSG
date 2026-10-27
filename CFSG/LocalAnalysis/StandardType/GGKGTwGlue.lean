module

public import CFSG.LocalAnalysis.StandardType.GGE6KGLayerInputTw
public import CFSG.LocalAnalysis.StandardType.GGKGTwFrame
public import CFSG.LocalAnalysis.StandardType.GGKGTwClausesA5D4
public import CFSG.LocalAnalysis.StandardType.GGKGTwClausesA3
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.NoOffRest CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem kgLayers_TwE6_of_layers (hD4 : GGTwE6D4LayerInput) (hA3 : GGTwE6A3LayerInput) :
    ∀ (n : ℕ), 1 ≤ n → 3 ∣ 2 ^ n + 1 → ∀ (K : Type) [Field K] [Finite K],
      Nat.card K = (2 ^ n) ^ 2 →
        GGE6KGLayers (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) := by
  intro n hn h3 K _ _ hK L' _ _ ψ A hTB h5
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := by
    obtain ⟨m, hprime, hm⟩ := FiniteField.card K (ringChar K)
    have hcard : Fintype.card K = 2 ^ (2 * n) := by
      rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, Nat.mul_comm]
    rw [hcard] at hm
    have hdvd : ringChar K ∣ 2 ^ (2 * n) := by
      rw [hm]
      exact dvd_pow_self _ m.pos.ne'
    have hrc : ringChar K = 2 :=
      (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow hprime hdvd)
    exact hrc ▸ ringChar.charP K
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : IsAlgClosed (AlgebraicClosure K) := AlgebraicClosure.isAlgClosed K
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 n
    with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have h30 : (3 : AlgebraicClosure K) ≠ 0 :=
    CFSG.HardMathSupport.Lang.E6Descent.three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.TwistedDiag.exists_cube_root
      (Ω := AlgebraicClosure K) h30
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  obtain ⟨v, g, κ, t, hF⟩ :=
    ggTwKGFrame_holds n hn h3 K hK σ hσ ε hε Fr hFr ζ hζ hζo L' ψ A hTB h5
  obtain ⟨hψ, hker, hperf, -, -, -, -, -⟩ := hTB
  refine ⟨fun c hc => ?_, fun a b hab => ?_⟩
  · exact kgL1_clause_tw TwE6RootAs.twE6CorootCore_holds hK hσ h3 hζo hψ hF c hc
  · obtain ⟨Ev, hEv, hl⟩ :=
      kgD4_clause_tw hD4 hn hK hσ h3 hζo hψ hker hperf hF hab
    obtain ⟨Eab, hEab, hu, hM⟩ :=
      kgA3_clause_tw hA3 hn hK hσ h3 hζo hψ hker hperf hF hab
    exact ⟨Ev, Eab, hEv, hEab, hu, hl, hM⟩

end CFSG.StandardType.KGL

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem largeEvenLabelAll_kgLayers_TwE6 (hD4 : KGL.GGTwE6D4LayerInput)
    (hA3 : KGL.GGTwE6A3LayerInput) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twE6) (h3 : 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGE6KGLayers R I := by
  refine TwE6Delta.labelAll (lab := lab) htag
    (Q := fun R _ I => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGE6KGLayers R I) ?_
  intro K _ _ hK
  intro _ _
  exact KGL.kgLayers_TwE6_of_layers hD4 hA3 lab.n hΛ.1 h3 K hK

theorem ggE6KGLayerInputTw_of_layers (hD4 : KGL.GGTwE6D4LayerInput)
    (hA3 : KGL.GGTwE6A3LayerInput) : GGE6KGLayerInputTw :=
  fun lab htag h3 hΛ => largeEvenLabelAll_kgLayers_TwE6 hD4 hA3 hΛ htag h3

end CFSG.StandardType

end
