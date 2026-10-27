module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Datum
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLang

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

theorem twistedConjOn_isRoot_E6 {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime) (hp2 : p ≠ 2) :
    TwistedConjOn K TwistTag.E6 n (IsRoot TwistTag.E6.tag) p := by
  unfold TwistedConjOn
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hperf, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hH : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K
      TwistTag.E6.perm n = graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    (twistedH_eq_commutator K TwistTag.E6 n σ.toRingHom hσ).trans hperf
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot TwistTag.E6.tag) K),
      H = graphFixedRootGroup TwistTag.E6 K σ.toRingHom →
      GGRawFieldConj p (LargeEvenCenterQuot H) (markIDImage (IsRoot TwistTag.E6.tag) K H)
        (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K H) from key _ hH
  intro H hH'
  subst hH'
  exact ggRawFieldConj_C0_E6 hn hK σ hσ hp hp2

theorem ggRawFieldConj_twE6 {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) :
    GGRawFieldConj p (LargeEvenCenterQuot
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K _)
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K _) := by
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  have : CharP K 2 := charP_two_of_card hK2
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have h := (twistedConjOn_isRoot_E6 hn hK σ hσ hp hp2).of_eq
    (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
        TwistTag.E6.perm n →
      GGRawFieldConj p (LargeEvenCenterQuot H) (LargeEvenChevIDImage TwistTag.E6.tag.cartan K H)
        (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K H) from
    key _ (largeEvenTwistedH_eq _ K _ n)
  intro H hH
  subst hH
  rw [largeEvenChevIDImage_eq]
  exact h

end RecipeExcLang

open RecipeExcLang

theorem ggRawFieldConjOn_twE6 :
    GGRawFieldConjOn fun _ lab => lab.tag = .twE6 := by
  intro p hp hp2 lab hlab ht Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  obtain ⟨hn, -⟩ := hlab
  dsimp only [LargeEvenRawDatum] at h ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggRawFieldConj_twE6 hn hK hp hp2⟩

theorem ggRawFieldConjOn_twisted :
    GGRawFieldConjOn fun p lab =>
      ¬ (lab.tag = .triD4 ∧ p = 3) ∧ GGRecipeTwistedConjLabel lab := by
  intro p hp hp2 lab hlab ⟨hne, hS⟩
  rcases hS with ht | ht
  · exact ggRawFieldConjOn_twE6 p hp hp2 lab hlab ht
  · exact ggRawFieldConjOn_triD4 p hp hp2 lab hlab ⟨hne, ht⟩

theorem ggRawFieldConjInputExc_holds :
    GGRawFieldConjInputExc :=
  ggRawFieldConjInputExc_of_twisted ggRawFieldConjOn_twisted

end CFSG.StandardType
