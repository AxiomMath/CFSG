module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1TwE6ThreeModel
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Holds
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Dvd
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALift

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.TableB CFSG.StandardType.S2MathAs51642Interfaces
open CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem q1TwE6Three_rank_of_recipe
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J)
    (θ : L ⧸ Subgroup.center L ≃* TwE6Delta.RecipeR K n)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hactors : ∀ b ∈ Bs, ∃ φ ∈ TwE6Delta.RecipeI K n,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    3 ^ 5 ≤ Nat.card (ggGamma L hN).range := by
  have hlab : LargeEvenInLambda2 (⟨.twE6, 0, n⟩ : LargeEvenLabel) := ⟨hn, rfl⟩
  have hsplit : LargeEvenSplit 3 (⟨.twE6, 0, n⟩ : LargeEvenLabel) :=
    Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, h3⟩)
  have hmark : GGInnerDiagOnLab GGTableBTwE6ThreeLabel 3 Bs L := by
    refine ⟨hcfg.data_L.2.2.2, ⟨.twE6, 0, n⟩, hlab, ?_⟩
    dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy]
    exact ⟨K, inferInstance, inferInstance, hK,
      (TwE6Dvd.isSimpleGroup_recipeR hn hK).1,
      (TwE6Dvd.isSimpleGroup_recipeR hn hK).2, θ, ⟨rfl, rfl, h3⟩, hsplit, hN, hactors⟩
  exact ggTwE6ThreeBstarRankInput_holds G 3 B Bs x L D J hcfg hmark hN



theorem q1TwE6Three_holds : Q1TwE6Three := by
  intro G _ _ p B Bs x L D J hcfg hmark
  classical
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hmark
  obtain ⟨R, _, I, F, _, _, θ, hsel, -, -⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨ht, hp, h3⟩ := hsel
  subst p
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h3 hΛ
  subst t
  have hn : 1 ≤ n := hΛ.1
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  obtain ⟨K, _, _, hK, -, -, θK, -, hN, hactors⟩ := hraw
  have : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobeniusEquiv_def _ 2 n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  let e : TwE6Delta.RecipeR K n ≃* twistedE6RootGroup K σ := ε.symm
  have hI : ∀ (b : G) (hb : b ∈ Bs), ggBeta L (θK.trans e) hN ⟨b, hb⟩ ∈
      twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
    intro b hb
    obtain ⟨φ, hφ, hind⟩ := hactors b⁻¹ (Bs.inv_mem hb)
    have heq : φ = ggLAut L θK ⟨b, hN hb⟩ := by
      ext r
      obtain ⟨q, rfl⟩ := θK.surjective r
      induction q using QuotientGroup.induction_on with
      | H z =>
        rw [ggLAut_apply]
        apply hind z (L.normalizerMonoidHom ⟨b, hN hb⟩ z)
        change b * (z : G) * b⁻¹ = (b⁻¹)⁻¹ * (z : G) * b⁻¹
        rw [inv_inv]
    change ggLAut L (θK.trans e) ⟨b, hN hb⟩ ∈ _
    rw [NbrLangTypeA.ggLAut_trans (K := L) θK e ⟨b, hN hb⟩, ← heq]
    have hφe : MulAut.congr e φ ∈ (RecipeExcLang.twConj K σ).range := by
      apply (hε (MulAut.congr e φ)).1
      change MulAut.congr ε (MulAut.congr ε.symm φ) ∈ TwE6Delta.RecipeI K n
      have hinv : MulAut.congr ε (MulAut.congr ε.symm φ) = φ := by
        apply MulEquiv.ext
        intro z
        change ε (ε.symm (φ (ε (ε.symm z)))) = φ z
        simp only [MulEquiv.apply_symm_apply]
      rw [hinv]
      exact hφ
    obtain ⟨w, hw⟩ := hφe
    rw [← range_twistedE6InndiagConj]
    refine ⟨⟨w.1, NoOffTwE6Three.twInndiagGroup_le_twistedE6InndiagGL σ w.2⟩, ?_⟩
    rw [← hw]
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    rfl
  have h5 := q1TwE6Three_rank_of_recipe hn hK h3 hcfg θK hN hactors
  refine ggInnerDiagOn_stdSub_of_quotient_components Nat.prime_three hcfg
    (θK.trans e) hN hI h5 ?_
  intro A hA hAI hcard u hu hu1 C hC
  exact Q1TwE6ThreeModel.q1TwE6ThreeModel_holds hn hK σ hσ h3 hA hAI hcard hu hu1 hC


theorem ggBstarInnerDiagJInput_of_not_e6Three_twE6Three
    (hrest : GGBstarInnerDiagJInputOn
      (fun p lab => ¬ E6Three p lab ∧ ¬ TwE6Three p lab)) : GGBstarInnerDiagJInput := by
  classical
  refine q1On_true_iff.mp ?_
  intro G _ _ p B Bs x L D J hcfg hmark
  refine (q1On_or hrest (q1On_or q1E6Three_holds q1TwE6Three_holds))
    G p B Bs x L D J hcfg ?_
  refine largeEvenMarking_mono (fun lab R _ I F θ h => ⟨?_, h.2⟩) hmark
  by_cases hE : E6Three p lab
  · exact Or.inr (Or.inl hE)
  · by_cases hT : TwE6Three p lab
    · exact Or.inr (Or.inr hT)
    · exact Or.inl ⟨hE, hT⟩

end CFSG.StandardType
