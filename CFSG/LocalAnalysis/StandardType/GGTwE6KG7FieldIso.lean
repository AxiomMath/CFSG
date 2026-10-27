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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7BaseChange

public section

namespace CFSG.StandardType.TwE6KG7

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent
  CFSG.StandardType.SCFourCover

private theorem kg7field_congr_trans {G H I : Type*} [Group G] [Group H] [Group I]
    (e : G ≃* H) (f : H ≃* I) (φ : MulAut G) :
    MulAut.congr (e.trans f) φ = MulAut.congr f (MulAut.congr e φ) := by
  ext x
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_trans_apply]

private theorem kg7field_congr_symm {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (φ : MulAut H) :
    (MulAut.congr e).symm φ = MulAut.congr e.symm φ := by
  ext x
  rfl

private theorem kg7field_congr_symm_trans {G₀ G₁ G₂ : Type*}
    [Group G₀] [Group G₁] [Group G₂]
    (a : G₁ ≃* G₀) (b : G₂ ≃* G₁) (φ : MulAut G₀) :
    MulAut.congr (a.symm.trans b.symm) φ =
      (MulAut.congr b).symm ((MulAut.congr a).symm φ) := by
  rw [kg7field_congr_trans a.symm b.symm φ]
  rw [← kg7field_congr_symm a φ]
  rw [← kg7field_congr_symm b ((MulAut.congr a).symm φ)]

theorem exists_recipeR_equiv_twC0
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ ψ : TwE6Delta.RecipeR K n ≃*
        ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * n)) (frobQ 2 n)),
      ∀ φ, φ ∈ TwE6Delta.RecipeI K n ↔ MulAut.congr ψ φ ∈ LayerSixE.twInndiagAut n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) hn hK
  let k := GaloisField 2 (2 * n)
  haveI : Fintype (GaloisField 2 (2 * n)) := Fintype.ofFinite _
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card (GaloisField 2 (2 * n)) = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      CFSG.LieType.Universal.card_galoisField_two_mul 2 n hn, hK]
  let τ : GaloisField 2 (2 * n) ≃+* K := FiniteField.ringEquivOfCardEq hcard
  have hfrob : ∀ c : GaloisField 2 (2 * n), frobQEquiv hn c = c ^ 2 ^ n :=
    fun c => frobQ_apply 2 n c
  have hτ : ∀ c, τ (frobQEquiv hn c) = σ (τ c) := by
    intro c
    rw [hfrob c, map_pow, hσ]
  obtain ⟨e, he⟩ := exists_twConj_range_baseChange τ (frobQEquiv hn) σ hτ
  let A : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
    (RecipeExcLang.twConj K σ).range
  let B : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 k (frobQ 2 n))) :=
    (RecipeExcLang.twConj k (frobQEquiv hn)).range
  have hrange : (TwE6Transport.recipeConj σ ε).range =
      A.map (MulAut.congr ε).toMonoidHom := by
    show (TwE6Transport.recipeConj σ ε).range =
      (RecipeExcLang.twConj K σ).range.map (MulAut.congr ε).toMonoidHom
    rw [TwE6Transport.recipeConj]
    exact MonoidHom.range_comp _ _
  have hB : B = LayerSixE.twInndiagAut n := by
    show (RecipeExcLang.twConj k (frobQEquiv hn)).range = LayerSixE.twInndiagAut n
    exact (twInndiagAut_eq_range_twConj hn).symm
  refine ⟨ε.symm.trans e.symm, fun φ => ?_⟩
  have hψ : MulAut.congr (ε.symm.trans e.symm) φ =
      (MulAut.congr e).symm ((MulAut.congr ε).symm φ) :=
    kg7field_congr_symm_trans ε e φ
  calc φ ∈ TwE6Delta.RecipeI K n
      ↔ φ ∈ (TwE6Transport.recipeConj σ ε).range := (hε φ).symm
    _ ↔ (MulAut.congr ε).symm φ ∈ A := by
          rw [hrange]
          exact Subgroup.mem_map_equiv
    _ ↔ (MulAut.congr e).symm ((MulAut.congr ε).symm φ) ∈ B := by
          have h := he ((MulAut.congr e).symm ((MulAut.congr ε).symm φ))
          have h' : (MulAut.congr e) ((MulAut.congr e).symm ((MulAut.congr ε).symm φ)) =
              (MulAut.congr ε).symm φ := MulEquiv.apply_symm_apply _ _
          exact (h.trans (by rw [h'])).symm
    _ ↔ (MulAut.congr e).symm ((MulAut.congr ε).symm φ) ∈ LayerSixE.twInndiagAut n := by
          rw [hB]
    _ ↔ MulAut.congr (ε.symm.trans e.symm) φ ∈ LayerSixE.twInndiagAut n := by
          rw [hψ]

end CFSG.StandardType.TwE6KG7
