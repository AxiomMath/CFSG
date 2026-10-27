module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImage
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGE6RankFiveTorality
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavMarking
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavHeartImage
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6R5Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6D5CoreFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgSetupUntw
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.L154ExcDataTw
public import CFSG.LieType.Chevalley.GraphFixedFinitePerfect

public noncomputable section

namespace CFSG.StandardType.QTwoE6

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.RecipeExcLang CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem rawDatum_legacy_to_canonical_twE6 {lab : LargeEvenLabel} (htag : lab.tag = .twE6)
    {Q : LargeEvenRawCont} (h : CFSG.Assembly.LargeEvenRawDatumLegacy lab Q) :
    CFSG.Assembly.LargeEvenRawDatum lab Q := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag
  subst htag
  dsimp only [CFSG.Assembly.LargeEvenRawDatum,
    CFSG.Assembly.LargeEvenRawDatumLegacy] at h ⊢
  exact h

theorem actual_beta_image_of_marking {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twE6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    {e : ℕ} (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ e) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
      (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (S : Subgroup (MulAut ↥(twistedE6RootGroup K σ))),
      Nat.card K = 4 ∧ (∀ c, σ c = c ^ 2) ∧
      S = (ggBeta L θ hN).range.map
        (MulAut.congr (centerQuotEquivOfBot
          (exceptional_fixed_center_trivial TwistTag.E6 K σ))).toMonoidHom ∧
      IsElemAbelian 3 S ∧ Nat.card S = 3 ^ e ∧
      S ≤ (CFSG.StandardType.RecipeExcLang.twConj K σ).range ∧
      (ggBeta L θ hN).range ≤
        markIDImage (Blueprint.Chevalley.IsRoot TwistTag.E6.tag) K
          (twistedE6RootGroup K σ) ∧
      IsElemAbelian 3 (ggBeta L θ hN).range ∧
      Nat.card (ggBeta L θ hN).range = 3 ^ e := by
  classical
  have hBs : IsElemAbelian p Bs := hS.1.1.2.1.2.1
  have hSS : LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hL : commutator L = ⊤ := hSS.2.2.2.1.2.2.1
  unfold GGInnerDiagOnLabel at hmark
  obtain ⟨-, labM, hlab2M, hrawM⟩ := hmark
  let Qmark : CFSG.Assembly.LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : L ⧸ Subgroup.center L ≃* R,
        (labM = lab) ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : G) = (b : G)⁻¹ * l * (b : G)) φ
  obtain ⟨R, _, I, F, hQraw⟩ := CFSG.StandardType.largeEvenRawDatum_exists hrawM
  obtain ⟨-, -, θR, hlabEq, hNR, -⟩ := hQraw
  have htagM : labM.tag = .twE6 := by rw [hlabEq]; exact htag
  have hltM : labM.n < 2 := by rw [hlabEq]; exact hq2
  have hnM : 1 ≤ labM.n := hlab2M.1
  have hn1 : labM.n = 1 := by omega
  have hrawCanon : CFSG.Assembly.LargeEvenRawDatum labM Qmark :=
    rawDatum_legacy_to_canonical_twE6 htagM hrawM
  obtain ⟨K, instF, instFin, σ, hKcard, hσpow, hQ0⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.excTwE6_raw_of_label (lab := labM) (Q := Qmark)
      htagM hnM hrawCanon
  obtain ⟨-, -, θ, -, hN, hact⟩ := hQ0
  have hK4 : Nat.card K = 4 := by
    rw [hKcard, hn1]
    norm_num
  have hσ : ∀ c, σ c = c ^ 2 := by
    simpa [hn1] using hσpow
  have hβI : (ggBeta L θ hN).range ≤
      markIDImage (Blueprint.Chevalley.IsRoot TwistTag.E6.tag) K
        (twistedE6RootGroup K σ) := by
    rintro _ ⟨b, rfl⟩
    simpa only [ggBeta_eq] using
      CFSG.StandardType.ggLAut_mem_of_induces (L := L) (θ := θ) (B := Bs) hN hact b.2
  have hBs3 : IsElemAbelian 3 Bs := by simpa [hp3] using hBs
  have hidx3 : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ e := by
    rw [hidx, hp3]
  have hβ := QTwoCav.beta_image_of_index hBs3 hL θ hN hidx3
  let eR := centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
  let Simg : Subgroup (MulAut ↥(twistedE6RootGroup K σ)) :=
    (ggBeta L θ hN).range.map (MulAut.congr eR).toMonoidHom
  have hSdef : Simg = (ggBeta L θ hN).range.map
      (MulAut.congr (centerQuotEquivOfBot
        (exceptional_fixed_center_trivial TwistTag.E6 K σ))).toMonoidHom := rfl
  have hSEA : IsElemAbelian 3 Simg := hβ.1.map (MulAut.congr eR).toMonoidHom
  have hScard : Nat.card Simg = 3 ^ e := by
    rw [show Simg = (ggBeta L θ hN).range.map
        (MulAut.congr eR).toMonoidHom from rfl,
      Subgroup.card_map_of_injective (MulAut.congr eR).injective, hβ.2]
  have hSrange : Simg ≤ (CFSG.StandardType.RecipeExcLang.twConj K σ).range := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨w, hw⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.K155X.excTwE6_exists_twConj_of_mem_markID σ (hβI hu)
    exact ⟨w, hw.symm⟩
  exact ⟨K, instF, instFin, σ, θ, hN, Simg, hK4, hσ, hSdef, hSEA, hScard,
    hSrange, hβI, hβ.1, hβ.2⟩

theorem actual_beta_langCube_of_marking {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp3 : p = 3)
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo p lab) (htag : lab.tag = .twE6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs L)
    {e : ℕ} (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = p ^ e)
    (he : 5 ≤ e) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K)
      (hK1 : Nat.card K = (2 ^ 1) ^ 2) (hσ1 : ∀ c, σ c = c ^ 2 ^ 1)
      (θ : L ⧸ Subgroup.center L ≃* LargeEvenCenterQuot (twistedE6RootGroup K σ))
      (hN : Bs ≤ Subgroup.normalizer (L : Set G))
      (S : Subgroup (MulAut ↥(twistedE6RootGroup K σ)))
      (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
      (g : ModGL .E6 (AlgebraicClosure K)),
      Nat.card K = 4 ∧ (∀ c, σ c = c ^ 2) ∧
      S = (ggBeta L θ hN).range.map
        (MulAut.congr (centerQuotEquivOfBot
          (exceptional_fixed_center_trivial TwistTag.E6 K σ))).toMonoidHom ∧
      IsElemAbelian 3 S ∧ Nat.card S = 3 ^ e ∧
      g ∈ adjointGroup .E6 (AlgebraicClosure K) ∧
      g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure K) Fr g =
        TwistedDiag.n0 (AlgebraicClosure K) ∧
      S ≤ CFSG.StandardType.TwE6DD2.langCube (n := 1) le_rfl hK1 σ hσ1 Fr hFr g ∧
      S ≤ (CFSG.StandardType.RecipeExcLang.twConj K σ).range := by
  obtain ⟨K, instF, instFin, σ, θ, hN, S, hK4, hσ, hSdef, hSEA, hScard, hSrange,
    -, -, -⟩ := actual_beta_image_of_marking hS hp3 hq2 htag hmark hidx
  have hK1 : Nat.card K = (2 ^ 1) ^ 2 := by
    rw [hK4]
    norm_num
  have hσ1 : ∀ c, σ c = c ^ 2 ^ 1 := by
    simpa using hσ
  let Ω := AlgebraicClosure K
  haveI : CharP K 2 := charP_two_of_card (m := 2) (by rw [hK4]; norm_num)
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : ExpChar Ω 2 := ExpChar.prime Nat.prime_two
  let Fr : Ω →+* Ω := iterateFrobenius Ω 2 1
  have hFr : ∀ c, Fr c = c ^ 2 ^ 1 := fun _ => rfl
  have h5 : 3 ^ 5 ≤ Nat.card S := by
    rw [hScard]
    exact Nat.pow_le_pow_right (by norm_num) he
  obtain ⟨g, hg, hgn, hSlang⟩ :=
    CFSG.StandardType.TwE6DD2.exists_cubeTorus_lang (n := 1) le_rfl hK1 σ hσ1
      (by norm_num) Fr hFr hSEA hSrange h5
  exact ⟨K, instF, instFin, σ, hK1, hσ1, θ, hN, S, Fr, hFr, g, hK4, hσ, hSdef,
    hSEA, hScard, hg, hgn, hSlang, hSrange⟩

end CFSG.StandardType.QTwoE6

end
