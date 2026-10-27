module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourModel
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverSetting
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourNotToral
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2


@[expose] def GGTwE6SCFourLabelsAd : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n),
    (∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range) →
    3 ∣ 2 ^ n + 1 → IsSimpleGroup (TwE6Delta.RecipeR K n) → Finite (TwE6Delta.RecipeR K n) →
    ∀ (A : Subgroup (MulAut (TwE6Delta.RecipeR K n))) (a₀ : MulAut (TwE6Delta.RecipeR K n))
      (J₁ : Subgroup (TwE6Delta.RecipeR K n)),
      GGTwE6SCFourSettingAd (TwE6Delta.RecipeI K n) A a₀ J₁ →
      ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε A) →
      LargeEvenMarking ↥J₁ fun lab' _ _ _ _ _ =>
        (lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
          lab' = ⟨.twA, 2, 3 * n⟩) ∨ lab' = ⟨.twA, 5, n⟩

theorem ggTwE6SCFourLabelsKnown_of_ad (h : GGTwE6SCFourLabelsAd) : GGTwE6SCFourLabelsKnown := by
  intro lab hlab ht h3
  refine TwE6Delta.labelAll ht fun K _ _ hK => ?_
  intro hs _ L' _ _ ψ hψ hker hL A a₀ J₁ hset
  have hn : 1 ≤ lab.n := hlab.1
  have hset' := hset
  obtain ⟨hE, hI, hcard, hSC, ha₀, -, hcomp, -, -⟩ := hset'
  obtain ⟨φ₀, -, hφ₀⟩ := hI a₀ ha₀
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := lab.n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hinj : Function.Injective (iterateFrobenius K 2 lab.n) :=
    (iterateFrobenius K 2 lab.n).injective
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ lab.n :=
    ⟨RingEquiv.ofBijective (iterateFrobenius K 2 lab.n)
      ⟨hinj, Finite.surjective_of_injective hinj⟩, fun c => iterateFrobenius_def 2 lab.n c⟩
  obtain ⟨Fr, hFr⟩ : ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
      ∀ c, Fr c = c ^ 2 ^ lab.n :=
    ⟨iterateFrobenius _ 2 lab.n, fun c => iterateFrobenius_def 2 lab.n c⟩
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  exact (largeEvenMarking_map_iff hker (commutator_eq_self_of_isComponentOf hcomp) _).2
    (h lab.n hn K hK σ hσ Fr hFr ε hε h3 hs (Finite.of_surjective ψ hψ) _ φ₀ (J₁.map ψ)
      (ggTwE6SCFourSetting_descend hψ hker hL hset hφ₀)
      (not_e6AdToral_rgrpModel hn hK σ hσ Fr hFr ε hε h3 hψ hker hL hE.2 hcard hI hSC))

end CFSG.StandardType.SCFourCover

end
