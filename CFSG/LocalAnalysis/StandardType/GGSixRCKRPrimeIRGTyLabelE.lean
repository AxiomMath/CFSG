module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGLabelDef
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelAux
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.Timmesfeld.RankTwo.Presentation

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem irg_hasLabel_exc
    {X : Type} [Group X] {J : Subgroup X} (hqs : CFSG.Assembly.IsQuasisimple ↥J)
    {t : StatedLieTag} {n g : ℕ} (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6)
    (hn : RCKNormalizedModel t n g) (φ : (ggU t n g).K →* X)
    (hr : φ.range = J) (hk : φ.ker ≤ Subgroup.center (ggU t n g).K) :
    GGHasLabel (irgLabel t n g) (↥J ⧸ Subgroup.center ↥J) := by
  have hM := irg_lieModel_quot hn.1 hn.2 φ hr hk
  have hex : ChevalleyExceptionalModel (↥J ⧸ Subgroup.center ↥J) t 2 g :=
    hM.chevalleyExceptionalModel (by rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide)
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨-, K, hF, hfin, hcard, ⟨e⟩⟩ := hex
    obtain ⟨e'⟩ := centerQuot_chevGroup_equiv K CFSG.Blueprint.Chevalley.Tag.F4
    exact ⟨K, hF, hfin, hcard, ⟨e.trans e'.symm⟩⟩
  · obtain ⟨-, K, hF, hfin, hcard, ⟨e⟩⟩ := hex
    obtain ⟨e'⟩ := centerQuot_chevGroup_equiv K CFSG.Blueprint.Chevalley.Tag.E6
    exact ⟨K, hF, hfin, hcard, ⟨e.trans e'.symm⟩⟩
  · obtain ⟨-, K, hF, hfin, hcard, ⟨e⟩⟩ := hex
    obtain ⟨e'⟩ := centerQuot_chevGroup_equiv K CFSG.Blueprint.Chevalley.Tag.E7
    exact ⟨K, hF, hfin, hcard, ⟨e.trans e'.symm⟩⟩
  · obtain ⟨-, K, hF, hfin, hcard, ⟨e⟩⟩ := hex
    obtain ⟨e'⟩ := centerQuot_chevGroup_equiv K CFSG.Blueprint.Chevalley.Tag.E8
    exact ⟨K, hF, hfin, hcard, ⟨e.trans e'.symm⟩⟩
  · obtain ⟨-, K, hF, hfin, hcard, σ, hσ, ⟨e⟩⟩ := hex
    obtain ⟨e'⟩ := centerQuot_twistedH_equiv K CFSG.Blueprint.Chevalley.TwistTag.E6 g σ hσ
    exact ⟨K, hF, hfin, hcard, ⟨e.trans e'.symm⟩⟩

theorem irg_hasLabel_tri
    {X : Type} [Group X] {J : Subgroup X} (hqs : CFSG.Assembly.IsQuasisimple ↥J)
    {F : Type} [Field F] [Finite F] {σ : F →+* F} {g : ℕ} (hT : TriField F σ g)
    (φ : (triD4Universal F σ).K →* X) (hr : φ.range = J)
    (hk : φ.ker ≤ Subgroup.center (triD4Universal F σ).K) :
    GGHasLabel ⟨.triD4, 0, g⟩ (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨hg, hFcard, hσq⟩ := hT
  have hmodel : CFSG.Blueprint.LieModel
      ((triD4Universal F σ).K ⧸ Subgroup.center (triD4Universal F σ).K) .trialityD4 0 2 g :=
    CFSG.Timmesfeld.lieModel_twistedD4_quotient Nat.prime_two hg hFcard σ hσq
  have hq2 : 2 ≤ 2 ^ g := le_trans Nat.prime_two.two_le (Nat.le_self_pow (by omega) 2)
  have hKq0 := CFSG.LieType.Steinberg.TwistedD4.twistedGroup_isQuasisimple_of_card hq2 hFcard hσq
  have hKq : CFSG.Open.IsQuasisimple (triD4Universal F σ).K :=
    ⟨Group.isPerfect_def.1 hKq0.1, hKq0.2.1⟩
  subst hr
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.HSubT.quotCenter_mulEquiv_of_surj hKq
    φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ) (fun x hx => hk
      (MonoidHom.mem_ker.mpr (congrArg Subtype.val hx)))
  have hM := CFSG.Blueprint.LieModel.of_mulEquiv e hmodel
  obtain ⟨-, K, hF, hfin, hcard, σ', hσ', ⟨e2⟩⟩ := hM.chevalleyExceptionalModel (by decide)
  obtain ⟨e3⟩ := centerQuot_twistedH_equiv K CFSG.Blueprint.Chevalley.TwistTag.D4 g σ' hσ'
  exact ⟨K, hF, hfin, hcard, ⟨e2.trans e3.symm⟩⟩

end CFSG.StandardType.RCKRP
