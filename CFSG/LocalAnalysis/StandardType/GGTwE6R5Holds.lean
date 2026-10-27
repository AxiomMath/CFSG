module

public import CFSG.LocalAnalysis.StandardType.GGTwE6R4Defs
public import CFSG.LocalAnalysis.StandardType.GGTwE6R5Torus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.Classical2


namespace TwE6R5

theorem not_le_inn_of_card {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) (h9 : ¬ 9 ∣ 2 ^ n + 1)
    {Y : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hY : IsElemAbelian 3 Y) (hYI : Y ≤ (RecipeExcLang.twConj K σ).range)
    (hYc : Nat.card Y = 3 ^ 6) :
    ¬ Y ≤ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hFr : ∀ c, iterateFrobenius (AlgebraicClosure K) 2 n c = c ^ 2 ^ n :=
    fun c => iterateFrobenius_def 2 n c
  obtain ⟨g, hg, hgn, rfl⟩ := TwE6DD2.exists_eq_langCube hn hK σ hσ h3 _ hFr hY hYI hYc
  exact langCube_not_le_inn hn hK σ hσ _ hFr h3 h9 hg hgn

end TwE6R5

theorem ggTwE6ThreeNoRankSixInput_holds : GGTwE6ThreeNoRankSixInput := by
  intro K _ _ n hn hK h3 h9 T hT hTc
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  obtain ⟨σ, hσ⟩ : ∃ σ : K ≃+* K, ∀ c, σ c = c ^ 2 ^ n :=
    ⟨RingEquiv.ofBijective (iterateFrobenius K 2 n) ⟨hinj, Finite.surjective_of_injective hinj⟩,
      fun c => iterateFrobenius_def 2 n c⟩
  obtain ⟨ε, -⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  have hc := CFSG.SeitzReduction.mulAut_conj_injective_of_center_eq_bot
    (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  have hE : Nat.card (T.map ε.symm.toMonoidHom) = 3 ^ 6 :=
    (Subgroup.card_map_of_injective (K := T) (f := ε.symm.toMonoidHom)
      fun a b h => ε.symm.injective h).trans hTc
  refine TwE6R5.not_le_inn_of_card hn hK σ hσ h3 h9
    ((hT.map ε.symm.toMonoidHom).map MulAut.conj) ?_
    ((Subgroup.card_map_of_injective hc).trans hE) (Subgroup.map_le_range _ _)
  rintro _ ⟨c, -, rfl⟩
  exact ⟨⟨c, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.2⟩,
    RecipeExcLang.twConj_of_mem_C0 σ c⟩

end CFSG.StandardType
