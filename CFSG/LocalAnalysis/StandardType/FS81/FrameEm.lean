module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLeviHom
public import CFSG.ClassicalInvolution.WeakCT.ExceptionalTwo
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.SpPair
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Certs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.LangFrame
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCriticalStandard
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate10
public import Certificates.Certificate10050
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate13659
public import Certificates.Certificate13660
public import Certificates.Certificate1952
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8117
public import Certificates.Certificate9

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Assembly CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld CFSG.LieType
open scoped MatrixGroups

theorem isEm_seven_of_marking {G : Type} [Group G] {Y : Subgroup G}
    (h : LargeEvenMarking Y fun lab _ _ _ _ _ =>
      markTag lab = .E7 ∧ markRank lab = 0 ∧ markChar lab = 2 ∧ markDeg lab = 1) :
    IsEm 7 Y := by
  obtain ⟨hY, ⟨t, l, n⟩, hlab, hraw⟩ := h
  refine ⟨hY, ⟨t, l, n⟩, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, htag, -, -, hdeg⟩
  refine ⟨hs, hna, θ, ?_⟩
  cases t <;> simp only [markTag] at htag <;> (try split_ifs at htag) <;>
    first
    | exact ⟨Or.inl ⟨rfl, rfl⟩, hlab.2, hdeg⟩
    | cases htag

theorem isEm_eight_of_marking {G : Type} [Group G] {Y : Subgroup G}
    (h : LargeEvenMarking Y fun lab _ _ _ _ _ =>
      markTag lab = .E8 ∧ markRank lab = 0 ∧ markChar lab = 2 ∧ markDeg lab = 1) :
    IsEm 8 Y := by
  obtain ⟨hY, ⟨t, l, n⟩, hlab, hraw⟩ := h
  refine ⟨hY, ⟨t, l, n⟩, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, htag, -, -, hdeg⟩
  refine ⟨hs, hna, θ, ?_⟩
  cases t <;> simp only [markTag] at htag <;> (try split_ifs at htag) <;>
    first
    | exact ⟨Or.inr ⟨rfl, rfl⟩, hlab.2, hdeg⟩
    | cases htag

theorem linearBlockStandardPair_eq_sup {X : Type} [Group X] {W U V : Subgroup X}
    (h : LinearBlockStandardPair (ZMod 2) W U V) : W = U ⊔ V := by
  obtain ⟨θ, c, hW, -, hor⟩ := h
  have htop : (B12 (ZMod 2)).map (MulAut.conj c⁻¹).toMonoidHom ⊔
      (B23 (ZMod 2)).map (MulAut.conj c⁻¹).toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, B12_sup_B23]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj c⁻¹).surjective
  rw [← hW, MonoidHom.range_eq_map, ← htop, Subgroup.map_sup]
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]

theorem linearBlockStandardPair_subgroupOf {X : Type} [Group X] {Y W U V : Subgroup X}
    (hU : U ≤ Y) (hV : V ≤ Y) (h : LinearBlockStandardPair (ZMod 2) W U V) :
    LinearBlockStandardPair (ZMod 2) (W.subgroupOf Y) (U.subgroupOf Y) (V.subgroupOf Y) := by
  have hWY : W ≤ Y := (linearBlockStandardPair_eq_sup h) ▸ sup_le hU hV
  obtain ⟨θ, c, hW, hker, hor⟩ := h
  have hθ : ∀ x, θ x ∈ Y := fun x => hWY (hW ▸ ⟨x, rfl⟩)
  have key : ∀ (B : Subgroup SL(3, ZMod 2)) (S : Subgroup X), S ≤ Y → B.map θ = S →
      B.map (θ.codRestrict Y hθ) = S.subgroupOf Y := by
    intro B S hS hB
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hS, ← hB]
    rfl
  refine ⟨θ.codRestrict Y hθ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map]
    exact key ⊤ W hWY (by rw [← MonoidHom.range_eq_map, hW])
  · intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  · rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨key _ _ hU h1, key _ _ hV h2⟩
    · exact Or.inr ⟨key _ _ hV h1, key _ _ hU h2⟩

theorem isEm_seven_of_frame {G : Type} [Group G] (U : Fin 7 → Subgroup G)
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 7, edgeE 7 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j)) :
    IsEm 7 (⨆ k, U k) ∧
      Subgroup.centralizer ((⨆ k, U k : Subgroup G) : Set G) ⊓ (⨆ k, U k) = ⊥ := by
  set Y := ⨆ k, U k with hY
  have hUY : ∀ k, U k ≤ Y := fun k => le_iSup U k
  have hgen : ⨆ k, (U k).subgroupOf Y = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp_rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hUY _)]
    exact hY.symm
  obtain ⟨Ψ, -, -, hqs, hcen, hlie⟩ := weakCT_e7_two (F := ZMod 2) (Nat.card_zmod 2)
    (fun k => (U k).subgroupOf Y) hgen
    (fun i j hij h1 h2 a ha b hb => Subtype.ext (hcomm i j hij h1 h2 a ha b hb))
    (fun i j hij => by
      obtain ⟨W, hW⟩ := hpair i j hij
      exact ⟨_, linearBlockStandardPair_subgroupOf (hUY i) (hUY j) hW⟩)
  have hZ : Subgroup.center Y = ⊥ := by
    rw [hcen, CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot, Subgroup.map_bot]
  refine ⟨isEm_seven_of_marking
    (CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot
      (Group.isPerfect_def.1 hqs.1) hlie), ?_⟩
  rw [inf_comm, CFSG.GroupTheory.inf_centralizer_eq_map_center, hZ, Subgroup.map_bot]

theorem isEm_eight_of_frame {G : Type} [Group G] (U : Fin 8 → Subgroup G)
    (hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 8, edgeE 8 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j)) :
    IsEm 8 (⨆ k, U k) ∧
      Subgroup.centralizer ((⨆ k, U k : Subgroup G) : Set G) ⊓ (⨆ k, U k) = ⊥ := by
  set Y := ⨆ k, U k with hY
  have hUY : ∀ k, U k ≤ Y := fun k => le_iSup U k
  have hgen : ⨆ k, (U k).subgroupOf Y = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp_rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hUY _)]
    exact hY.symm
  obtain ⟨Ψ, -, -, hqs, hcen, hlie⟩ := weakCT_e8_two (F := ZMod 2) (Nat.card_zmod 2)
    (fun k => (U k).subgroupOf Y) hgen
    (fun i j hij h1 h2 a ha b hb => Subtype.ext (hcomm i j hij h1 h2 a ha b hb))
    (fun i j hij => by
      obtain ⟨W, hW⟩ := hpair i j hij
      exact ⟨_, linearBlockStandardPair_subgroupOf (hUY i) (hUY j) hW⟩)
  have hZ : Subgroup.center Y = ⊥ := by
    rw [hcen, CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.map_bot]
  refine ⟨isEm_eight_of_marking
    (CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot
      (Group.isPerfect_def.1 hqs.1) hlie), ?_⟩
  rw [inf_comm, CFSG.GroupTheory.inf_centralizer_eq_map_center, hZ, Subgroup.map_bot]

end CFSG.StandardType.FrameRoute.FS81
