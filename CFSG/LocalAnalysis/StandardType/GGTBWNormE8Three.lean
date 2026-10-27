module

public import CFSG.LocalAnalysis.StandardType.GGExcToralInnerAction
public import CFSG.LocalAnalysis.StandardType.GGTBTorE8Cover
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE8Three
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrKnownLemmas
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLParity

public noncomputable section

namespace CFSG.StandardType.E8ThreeWNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TableBExc


theorem card_lt_of_nonToral {K : Type} [Field K] [Finite K] [CharP K 2]
    (E : Subgroup (adjointGroup Tag.E8 K)) (hE : IsElemAbelian 3 E)
    (hNT : ¬ ExcFramesHalf.IsToralSubgroup Tag.E8 (AlgebraicClosure K)
      (E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup Tag.E8 K).subtype))) :
    Nat.card E < 3 ^ 7 := by
  classical
  by_contra h
  have h' := not_lt.mp h
  apply hNT
  have h3K : ¬ 3 ∣ Nat.card K := by
    let : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hKf]
    intro h3
    have h32 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hinj : Function.Injective ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (adjointGroup Tag.E8 K).subtype) := fun x y hxy =>
    Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) hxy)
  refine ExcFramesHalf.bigElemAbelianToralBar_E8_three K h3K _ ?_ ?_ ?_ ?_
  · rintro _ ⟨x, -, rfl⟩
    exact baseChangeGL_mem_adjointGroup _ x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hxy : x * y = y * x := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact h'

theorem ggTorusLift_E8_three_seven {K : Type} [Field K] [Finite K] [CharP K 2] :
    GGTorusLift 3 7 (RecipeGroup Tag.E8 K) := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hKf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hKf]
  rcases SCFourCover.three_dvd_two_pow_add_one_or_sub_one (f : ℕ) with h3 | h3
  · exact ggTorusLift_E8Plus Nat.prime_three (by norm_num) (by rw [hK]; exact h3)
  · exact ggTorusLift_mono Nat.prime_three
      (TableBExc.ggTorusLift_E8 Nat.prime_three (by norm_num) (by rw [hK]; exact h3))
      (by norm_num)

theorem ggTorusWNormSCLift_recipe_E8_three {K : Type} [Field K] [Finite K] [CharP K 2] :
    GGTorusWNormSCLift 3 (RecipeGroup Tag.E8 K) (RecipeID Tag.E8 K) := by
  intro L _ _ ψ hψ hker hperf A hA hAI h27 hsc hrank _ Γ _ _ M C V _ _ ι φ h α _ _ _ _ hgen s hs
  obtain ⟨e, -, E, hE, hEcard, -, hAE⟩ :=
    exists_e8_model_of_tableB (r := 3) ψ A ⟨hψ, hker, hperf, hA, hAI, h27, h27, hsc⟩
  have hlift : GGTorusLift 3 7 (RecipeGroup Tag.E8 K) := by
    exact ggTorusLift_E8_three_seven
  have h7 : 3 ^ 7 ≤ Nat.card E := hEcard ▸ hrank 7 hlift
  have hT : ExcFramesHalf.IsToralSubgroup Tag.E8 (AlgebraicClosure K)
      (E.map ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup Tag.E8 K).subtype)) := by
    by_contra hNT
    exact absurd h7 (not_le.mpr (card_lt_of_nonToral E hE hNT))
  exact ExcToralInner.ggWNormConcl_of_toral (Or.inr rfl) A e E hE hAE hT ι φ h α hgen hs

theorem largeEvenLabelAll_wnormLift_E8_three {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E8) : LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSCLift 3 R I := by
  obtain ⟨t, r, f⟩ := lab
  have hf : 1 ≤ f := hlab.1
  dsimp only at htag ⊢
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  let : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  exact ⟨K, i1, i2, hK, hQK, ggTorusWNormSCLift_recipe_E8_three⟩

end CFSG.StandardType.E8ThreeWNorm
