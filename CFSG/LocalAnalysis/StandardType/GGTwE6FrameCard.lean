module

public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTwE6
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Datum
public import CFSG.LieType.Steinberg.Exceptional.Fields

public section

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace CFSG.StandardType.TwE6FrameCard

theorem three_pow_five_le_card_of_maximal
    {f : ℕ} (h3 : 3 ∣ 2 ^ f + 1)
    {M' S : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))}
    (hInn : (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))).range ≤ M')
    (hmax : ∀ X : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f))), X ≤ M' → IsElemAbelian 3 X → Nat.card X ≤ Nat.card S) :
    3 ^ 5 ≤ Nat.card S := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · norm_num at h3
    · exact hf
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * f)
  let σ : K ≃+* K :=
    RingEquiv.ofBijective (frobQ 2 f)
      ⟨RingHom.injective _, Finite.surjective_of_injective (RingHom.injective _)⟩
  have hσ : ∀ c : K, σ c = c ^ (2 ^ f) := fun c => by
    change iterateFrobenius K 2 f c = c ^ (2 ^ f)
    exact iterateFrobenius_def 2 f c
  have hK : Nat.card K = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  let C := ↥(graphFixedRootGroup TwistTag.E6 K (frobQ 2 f))
  have hconj_inj : Function.Injective (MulAut.conj : C →* MulAut C) := by
    intro a b hab
    have h1 : RecipeExcLang.twConj K σ
          ⟨a, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ a.2⟩ =
        RecipeExcLang.twConj K σ
          ⟨b, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ b.2⟩ := by
      rw [RecipeExcLang.twConj_of_mem_C0 σ a, RecipeExcLang.twConj_of_mem_C0 σ b]
      exact hab
    have h2 := NoOffTwE6Three.twConj_injective hf hK σ hσ h1
    have hab' : (a : ModGL TwistTag.E6.tag K) = (b : ModGL TwistTag.E6.tag K) :=
      congrArg (fun w : ↥(RecipeExcLang.twInndiagGroup K σ) => (w : ModGL TwistTag.E6.tag K)) h2
    exact Subtype.ext hab'
  have h2f : (((2 ^ f : ℕ)) : ZMod 3) = -1 := by
    have h := (ZMod.natCast_eq_zero_iff (2 ^ f + 1) 3).2 h3
    rw [Nat.cast_add, Nat.cast_one] at h
    rw [add_eq_zero_iff_eq_neg] at h
    exact h
  have hneg : orderOf (-1 : ZMod 3) = 2 := by
    exact orderOf_eq_prime (by decide) (by decide)
  have he : orderOf (((2 ^ f : ℕ)) : ZMod 3) = 2 := by
    rw [h2f, hneg]
  obtain ⟨E, hE, hEcard⟩ :=
    CFSG.StandardType.exists_twistedE6 (ℓ := 2) (f := f) Nat.prime_two hf K hK σ hσ
      (p := 3) (e := 2) Nat.prime_three (by norm_num) he
  have hdeg : CFSG.LieType.SeitzGeneration.degCountTw 2 - 1 = 5 := by decide
  have hEcard' : 3 ^ 5 ≤ Nat.card E := by simpa [hdeg] using hEcard
  let X : Subgroup (MulAut C) := E.map (MulAut.conj : C →* MulAut C)
  have hXel : IsElemAbelian 3 X := hE.map (MulAut.conj : C →* MulAut C)
  have hXrange : X ≤ (MulAut.conj : C →* MulAut C).range := by
    change E.map (MulAut.conj : C →* MulAut C) ≤ (MulAut.conj : C →* MulAut C).range
    exact Subgroup.map_le_range _ E
  have hXle : X ≤ M' := hXrange.trans hInn
  have hXcard : Nat.card X = Nat.card E := Subgroup.card_map_of_injective hconj_inj
  have hmaxX : Nat.card X ≤ Nat.card S := hmax X hXle hXel
  calc
    3 ^ 5 ≤ Nat.card E := hEcard'
    _ = Nat.card X := hXcard.symm
    _ ≤ Nat.card S := hmaxX

end CFSG.StandardType.TwE6FrameCard
