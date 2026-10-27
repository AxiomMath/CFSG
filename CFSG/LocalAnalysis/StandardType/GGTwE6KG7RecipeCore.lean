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
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7LangTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7InnDiagConj
public import CFSG.LocalAnalysis.StandardType.GGTwE6KG7CanonLegacy

public section

namespace CFSG.StandardType.TwE6KG7

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent
  CFSG.StandardType.SCFourCover

theorem recipe_core
    (hT : CFSG.LocalAnalysis.GLTheoremA.T171Sh.TwE6W0ToralComponentAction)
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {Y : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hY : IsElemAbelian 3 Y)
    (hYI : ∀ φ ∈ Y, φ ∈ TwE6Delta.RecipeI K n) (hYc : Nat.card Y = 3 ^ 6)
    {d : MulAut (TwE6Delta.RecipeR K n)} (hdY : d ∈ Y) (hd1 : d ≠ 1)
    {Kc : Subgroup (TwE6Delta.RecipeR K n)} (hKc : IsComponentOf Kc (ggFix d))
    {φ : MulAut (TwE6Delta.RecipeR K n)} (hφY : φ ∈ Y) (hφKc : ∀ x ∈ Kc, φ x ∈ Kc) :
    LargeEvenMarking ↥Kc fun _ _ _ I _ θ =>
      ∃ ψ ∈ I, LargeEvenInduces θ
        (fun l l' : ↥Kc => (l' : TwE6Delta.RecipeR K n) = φ l) ψ := by
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) hn hK
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n :=
    fun c => iterateFrobenius_def (R := AlgebraicClosure K) 2 n c
  obtain ⟨g, hgadj, hgconj, hlang⟩ :=
    exists_lang_torus_of_rankSix hn hK h3 σ hσ ε hε hY hYI hYc Fr hFr
  obtain ⟨wd, hwd_eq, hwdT⟩ := hlang d hdY
  obtain ⟨wb, hwb_eq, hwbT⟩ := hlang φ hφY
  have hwd3 : wd ^ 3 = 1 := by
    apply TwE6Transport.recipeConj_injective σ ε hn hK hσ
    rw [map_pow, hwd_eq, hY.2 d hdY, map_one]
  have hwd1 : wd ≠ 1 := by
    intro hw
    exact hd1 (by rw [← hwd_eq, hw, map_one])
  have hwb3 : wb ^ 3 = 1 := by
    apply TwE6Transport.recipeConj_injective σ ε hn hK hσ
    rw [map_pow, hwb_eq, hY.2 φ hφY, map_one]
  have hfix : ggFix d = CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
      (TwE6Transport.recipeConj σ ε wd) := by
    rw [hwd_eq]
    exact Subgroup.ext fun _ => Iff.rfl
  have hKc' : IsComponentOf Kc
      (CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
        (TwE6Transport.recipeConj σ ε wd)) := hfix ▸ hKc
  have hφKc' : ∀ x ∈ Kc, TwE6Transport.recipeConj σ ε wb x ∈ Kc := by
    intro x hx
    rw [hwb_eq]
    exact hφKc x hx
  have hTorus : ∀ w ∈ ({wd, wb} : Set ↥(RecipeExcLang.twInndiagGroup K σ)),
      g⁻¹ * ((NoOffTwE6Three.twInndiagEquivRgrp hn hK σ hσ Fr hFr w :
          ↥(TwistedDiag.Rgrp (AlgebraicClosure K) Fr)) :
            ModGL Tag.E6 (AlgebraicClosure K)) * g ∈
        torusGroup Tag.E6 (AlgebraicClosure K) := by
    intro w hw
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hwdT
    · exact hwbT
  have hInn := hT n K hn hK h3 σ hσ ε wd wb hwd3 hwd1 hwb3 Fr hFr g hgadj hgconj hTorus
    Kc hKc' hφKc'
  rw [hwb_eq] at hInn
  exact legacyMarking_of_canonical_induces hφKc (hY.2 φ hφY)
    (marking_induces_of_innDiagOn_conj (TwE6Delta.center_recipeR_eq_bot hn hK) hKc hInn)

end CFSG.StandardType.TwE6KG7
