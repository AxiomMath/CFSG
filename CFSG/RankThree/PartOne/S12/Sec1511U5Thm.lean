module

public import CFSG.RankThree.PartOne.S12.Sec1511AU5
public import CFSG.RankThree.PartOne.S12.Sec1511U5Mod
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S12.Sec1322Fin
public import CFSG.RankThree.PartOne.S12.Sec136Inputs
public import CFSG.RankThree.PartOne.S12.Sec136Pair
public import CFSG.RankThree.PartOne.S12.Sec136Setup
public import CFSG.RankThree.PartOne.S12.Sec138Loc
public import CFSG.RankThree.PartOne.S12.Sec141Row
public import CFSG.RankThree.PartOne.S12.Sec1511Y3
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.RankThreeEven CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartTwo.Sec4

namespace Sec1511

theorem kfU5Irr : KFU5Irr := by
  intro f hf1 hf5 Ab hAbD hAbel hAbcard xb hxb hxb5 hnt Rb hRb hAbR hxR
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have := hAbel
  have hh := U5K.u5FieldData f hf1
  let e : MulAut (projSU 5 2 f) ≃* MulAut (primeFormP (U5K.u5FieldData f hf1)
      (KCUnitaryModel.idGram (GaloisField 2 (2 * f)) 5)) := MulAut.congr (U5K.u5Equiv f hf1)
  have hker : ∀ a ∈ Ab, e a ∈ primeFormD (U5K.u5FieldData f hf1)
      (KCUnitaryModel.idGram (GaloisField 2 (2 * f)) 5) := by
    intro a ha
    have h1 : a ∈ (U5K.u5FieldFactor f hf1).ker := by
      have := hAbD ha
      simpa [U5K.U5Inndiag, hf1] using this
    rw [← ker_primeFormFieldFactor (U5K.u5FieldData f hf1)
      (isPrimeFormGram_one_GL (n := 5) (K := GaloisField 2 (2 * f))) (by norm_num) (by omega)]
    exact h1
  have hRb' := U5M.kfU5Irr_model (h := U5K.u5FieldData f hf1) hf5 (Ab.map e.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact hker a ha)
    (IsElementaryAbelian.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective]; exact hAbcard)
    (e xb) (Subgroup.le_normalizer_map e.toMonoidHom ⟨xb, hxb, rfl⟩)
    (by rw [← map_pow, hxb5, map_one])
    (by
      obtain ⟨a, ha, hne⟩ := hnt
      refine ⟨e a, ⟨a, ha, rfl⟩, fun hc => hne (e.injective ?_)⟩
      simpa using hc)
    (Rb.map e.toMonoidHom) (hRb.map e.toMonoidHom)
    (by
      rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.le_normalizer_map e.toMonoidHom ⟨a, hAbR ha, rfl⟩)
    (Subgroup.le_normalizer_map e.toMonoidHom ⟨xb, hxR, rfl⟩)
  exact (Subgroup.map_eq_bot_iff_of_injective Rb e.injective).1 hRb'

theorem kf1511A_of_package (h1510 : Node1510) (hU5 : U5FiveInndiag) (hMod : KFU5Mod)
    (hAt : KFU5At) : KF1511A :=
  kf1511A_of_inputs h1510 hU5 hMod hAt kfU5Irr

end Sec1511

end CFSG.RankThree.PartOne
