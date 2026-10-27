module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.LocalAnalysis.StandardType.GGMarkingAllInduces
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117

public section

namespace CFSG.StandardType.TwE6KG7

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent
  CFSG.StandardType.SCFourCover

private theorem kg7lang_card_comap {G H : Type*} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {Y : Subgroup H} (hY : Y ≤ f.range) :
    Nat.card (Y.comap f) = Nat.card Y := by
  rw [← Subgroup.card_map_of_injective hf, Subgroup.map_comap_eq, inf_eq_right.2 hY]

private theorem kg7lang_recipeConj_range_le_congr
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    {R : Type*} [Group R] (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* R) :
    (TwE6Transport.recipeConj σ ε).range ≤ (MulAut.congr ε).toMonoidHom.range := by
  rintro φ ⟨w, rfl⟩
  exact ⟨RecipeExcLang.twConj K σ w, rfl⟩

private theorem kg7lang_exists_langCube
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ φ, φ ∈ (TwE6Transport.recipeConj σ ε).range ↔ φ ∈ TwE6Delta.RecipeI K n)
    {Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hY : IsElemAbelian 3 Y)
    (hYI : ∀ φ ∈ Y, φ ∈ TwE6Delta.RecipeI K n) (hYc : Nat.card Y = 3 ^ 6)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n) :
    ∃ g ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
      g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure K) Fr g =
          TwistedDiag.n0 (AlgebraicClosure K) ∧
      Y.comap (MulAut.congr ε).toMonoidHom =
        TwE6DD2.langCube hn hK σ hσ Fr hFr g := by
  have hYle : Y ≤ (TwE6Transport.recipeConj σ ε).range :=
    fun φ hφ => (hε φ).2 (hYI φ hφ)
  have hYle' : Y ≤ (MulAut.congr ε).toMonoidHom.range :=
    hYle.trans (kg7lang_recipeConj_range_le_congr σ ε)
  have hY'ea : IsElemAbelian 3 (Y.comap (MulAut.congr ε).toMonoidHom) :=
    hY.comap (MulAut.congr ε).injective
  have hY'card : Nat.card (Y.comap (MulAut.congr ε).toMonoidHom) = 3 ^ 6 := by
    rw [kg7lang_card_comap (f := (MulAut.congr ε).toMonoidHom)
      (MulAut.congr ε).injective hYle', hYc]
  have hY'range : Y.comap (MulAut.congr ε).toMonoidHom ≤
      (RecipeExcLang.twConj K σ).range :=
    TwE6Transport.comap_congr_le_range σ ε hYle
  obtain ⟨g, hg, hgn, hlang⟩ :=
    TwE6DD2.exists_eq_langCube hn hK σ hσ h3 Fr hFr hY'ea hY'range hY'card
  exact ⟨g, hg, hgn, hlang⟩

theorem exists_lang_torus_of_rankSix
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)
    (hε : ∀ φ, φ ∈ (TwE6Transport.recipeConj σ ε).range ↔ φ ∈ TwE6Delta.RecipeI K n)
    {Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hY : IsElemAbelian 3 Y)
    (hYI : ∀ φ ∈ Y, φ ∈ TwE6Delta.RecipeI K n) (hYc : Nat.card Y = 3 ^ 6)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2 ^ n) :
    ∃ g ∈ adjointGroup Tag.E6 (AlgebraicClosure K),
      g⁻¹ * CFSG.RankThree.Classical2.twistE6 (AlgebraicClosure K) Fr g =
          TwistedDiag.n0 (AlgebraicClosure K) ∧
        ∀ φ ∈ Y, ∃ w : ↥(RecipeExcLang.twInndiagGroup K σ),
          TwE6Transport.recipeConj σ ε w = φ ∧
            g⁻¹ * ((NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr w :
                ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr)) :
                  ModGL Tag.E6 (AlgebraicClosure K)) * g ∈
              torusGroup Tag.E6 (AlgebraicClosure K) := by
  obtain ⟨g, hg, hgn, hlang⟩ :=
    kg7lang_exists_langCube hn hK h3 σ hσ ε hε hY hYI hYc Fr hFr
  refine ⟨g, hg, hgn, ?_⟩
  intro φ hφ
  have hψY' : (MulAut.congr ε).symm φ ∈ Y.comap (MulAut.congr ε).toMonoidHom := by
    rw [Subgroup.mem_comap]
    change (MulAut.congr ε) ((MulAut.congr ε).symm φ) ∈ Y
    rw [MulEquiv.apply_symm_apply]
    exact hφ
  have hψlang : (MulAut.congr ε).symm φ ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g := by
    rw [← hlang]
    exact hψY'
  obtain ⟨b, _hb3, hx, hxeq⟩ :=
    (TwE6DD2.mem_langCube hn hK σ hσ Fr hFr (g := g)).1 hψlang
  let w : ↥(RecipeExcLang.twInndiagGroup K σ) :=
    (NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr).symm ⟨_, hx⟩
  have hw_eq : NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr w = ⟨_, hx⟩ :=
    MulEquiv.apply_symm_apply _ _
  have htw : RecipeExcLang.twConj K σ w = (MulAut.congr ε).symm φ := by
    have h := NoOffTwE6Three.rgrpConjAut_apply_baseChange hn hK σ hσ Fr hFr w
    rw [hw_eq] at h
    exact h.symm.trans hxeq
  have hrecipe : TwE6Transport.recipeConj σ ε w = φ := by
    rw [TwE6Transport.recipeConj_eq, htw]
    exact MulEquiv.apply_symm_apply (MulAut.congr ε) φ
  refine ⟨w, hrecipe, ?_⟩
  let d : ModGL Tag.E6 (AlgebraicClosure K) :=
    CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E6 b
  have hxval : ((NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr w :
      ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr)) : ModGL Tag.E6 (AlgebraicClosure K)) =
      g * d * g⁻¹ := by
    rw [hw_eq]
  rw [hxval]
  have hconj : g⁻¹ * (g * d * g⁻¹) * g = d := by
    group
  rw [hconj]
  exact rootDiagUnit_mem_torusGroup (τ := Tag.E6) b

end CFSG.StandardType.TwE6KG7
