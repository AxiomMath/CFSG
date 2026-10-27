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
public import Certificates.Certificate43
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
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13657
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7RankSix
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7RecipeCore
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7Unpack
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7Glue
import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Holds
import CFSG.LocalAnalysis.StandardType.GGTwE6TInHolds
import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKFinal
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeAssemblyHolds
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.F151DiagDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeD4ThreeHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6KernelExitFacts
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcAdj
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeExcInnerD4FixMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamChar2
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInBCDCharTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriLang
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamTriMain
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeLinStatedInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeReeF4LargeRFHolds
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6CompAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwE6Conn
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeTwSmall
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeUniInner
import CFSG.Quasithin.Background.B1
import CFSG.Quasithin.Background.B3Q
import CFSG.Quasithin.Background.B3ThreeModel
import CFSG.Quasithin.Background.B3ThreeStruct
import CFSG.Quasithin.Background.G2Omega4PlusModule
import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompO
import CFSG.Quasithin.EmptyFaithful.R3c19B
import CFSG.Quasithin.EmptyFaithful.S143FF
import CFSG.Quasithin.EmptyFaithful.S143Final
import CFSG.Quasithin.EmptyFaithful.S143HD
import CFSG.Quasithin.EmptyFaithful.S143IG
import CFSG.Quasithin.EmptyFaithful.S143JB
import CFSG.Quasithin.EmptyFaithful.S143KO
import CFSG.Quasithin.EmptyFaithful.S143KP
import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15421
import CFSG.RankThree.PartOne.N143.HighEvenU

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTwE6InnerDiagInput_holds :
    GGTwE6InnerDiagInput := by
  intro X _ _ hX A δ J hloc hcard hU2 hmark
  obtain ⟨hA3, hδA, hδ1, hJcomp, hAJ⟩ := hloc
  obtain ⟨U, hUne, hUpgrp, hAU⟩ := hU2
  obtain ⟨n, K, hfld, hfin, hn, h3, hKcard, θ, hθI⟩ :=
    TwE6KG7.exists_recipe_of_marking hmark
  letI : Field K := hfld
  letI : Finite K := hfin
  let ψ : X →* TwE6Delta.RecipeR K n :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  let ρ : MulAut X →* MulAut (TwE6Delta.RecipeR K n) := ggInducedAut θ
  have hψ_apply : ∀ x : X, ψ x = θ (x : X ⧸ Subgroup.center X) := fun _ => rfl
  have hρ : ∀ a l, ρ a (ψ l) = ψ (a l) := fun a l => ggInducedAut_apply θ a l
  have hρinj : Function.Injective ρ := ggInducedAut_injective_of_perfect hX θ
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨q, hq⟩ := θ.surjective y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (N := Subgroup.center X) q
    exact ⟨x, by
      rw [show ψ x = θ (QuotientGroup.mk' (Subgroup.center X) x) from rfl, hx, hq]⟩
  have hkerψ : ψ.ker ≤ Subgroup.center X := by
    intro x hx
    rw [MonoidHom.mem_ker, hψ_apply] at hx
    exact (QuotientGroup.eq_one_iff x).1 (θ.injective (by rw [hx, map_one]))
  have hR6 : NoOffTwE6Three.GGTwE6ThreeTwoLocalRankSixInput :=
    NoOffTwE6Three.ggTwE6ThreeTwoLocalRankSixInput_of_kg
      NoOffTwE6Three.ggTwE6ThreeTwoLocalInnToralInput_holds
      TwE6LemmaK.ggTwE6ThreeToralTypeMinusOneInput
  have hSel : IsElemAbelian 3 (A.map ρ) := CFSG.Open.IsElemAbelian.map hA3 ρ
  have hSI : ∀ φ ∈ A.map ρ, φ ∈ TwE6Delta.RecipeI K n := by
    rintro φ ⟨a, ha, rfl⟩
    exact hθI a ha
  have hScard : Nat.card (A.map ρ) = 3 ^ 4 :=
    (Subgroup.card_map_of_injective hρinj).trans hcard
  have hUne' : U.map ρ ≠ ⊥ := fun h =>
    hUne ((Subgroup.map_eq_bot_iff_of_injective U hρinj).1 h)
  have hU2' : IsPGroup 2 (U.map ρ) := IsPGroup.map hUpgrp ρ
  have hSU : ∀ s ∈ A.map ρ, ∀ u ∈ U.map ρ, s * u * s⁻¹ ∈ U.map ρ := by
    rintro s ⟨a, ha, rfl⟩ u ⟨v, hv, rfl⟩
    exact ⟨a * v * a⁻¹, hAU a ha v hv, by simp [map_mul, map_inv]⟩
  obtain ⟨Y, hAbar_le_Y, hYI, hYel, hYcard⟩ :=
    TwE6KG7.exists_rankSix_recipe_aut hR6 hn hKcard h3 hSel hSI hScard hUne' hU2' hSU
  have hT : CFSG.LocalAnalysis.GLTheoremA.T171Sh.TwE6W0ToralComponentAction :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.twE6W0ToralComponentAction_of_kernel
      CFSG.LocalAnalysis.GLTheoremA.T171Sh.excKernelCompAction_holds
      CFSG.LocalAnalysis.GLTheoremA.T171Sh.twE6ToralLangSetup_holds
      (CFSG.LocalAnalysis.GLTheoremA.T171Sh.KExit.twE6ToralKernelExit_of
        CFSG.LocalAnalysis.GLTheoremA.T171Sh.innerD4FixedPointsPerfect_holds)
      CFSG.LocalAnalysis.GLTheoremA.T171Sh.twE6ToralLangSetupH360_holds
  have hfix : ggAutFixedSubgroup δ = ggFix δ := Subgroup.ext fun _ => Iff.rfl
  have hJcompFix : IsComponentOf J (ggFix δ) := hfix ▸ hJcomp
  have hJp : ⁅J, J⁆ = J := SCFourCover.commutator_eq_self_of_isComponentOf hJcomp
  have hJmapComp : IsComponentOf (J.map ψ) (ggFix (ρ δ)) :=
    (SCFourCover.isComponentOf_map_iff hψsurj hkerψ (fun l => hρ δ l) hJp).1 hJcompFix
  have hnorm : ∀ a ∈ A, ∀ x ∈ J.map ψ, ρ a x ∈ J.map ψ := fun a ha =>
    (SCFourCover.mapsTo_map_iff hkerψ (fun l => hρ a l) hJp).1 (hAJ a ha)
  have hper : ∀ a ∈ A, LargeEvenMarking ↥(J.map ψ) fun _ _ _ I _ θ' =>
      ∃ φ ∈ I, LargeEvenInduces θ'
        (fun m m' : ↥(J.map ψ) => (m' : TwE6Delta.RecipeR K n) = ρ a m) φ := by
    intro a ha
    exact TwE6KG7.recipe_core (hT := hT) (hn := hn) (hK := hKcard) (h3 := h3)
      (hY := hYel) (hYI := hYI) (hYc := hYcard)
      (hdY := hAbar_le_Y ⟨δ, hδA, rfl⟩)
      (hd1 := fun h => hδ1 (hρinj (by rw [h, map_one])))
      (hKc := hJmapComp)
      (hφY := hAbar_le_Y ⟨a, ha, rfl⟩)
      (hφKc := hnorm a ha)
  exact TwE6KG7.ggMarkingAll_autsInduceOn_of_map
    ggRawInnFieldInput_holds
    (ggRawInndiagIsoInput_of_rest
      (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds))
    hkerψ A ρ hρ hJp hAJ hper

end CFSG.StandardType
