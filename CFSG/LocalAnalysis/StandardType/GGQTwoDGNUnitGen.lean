module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNativeGen
public import CFSG.LocalAnalysis.StandardType.GGQTwoSU34
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitUnitaryGeometry
public import CFSG.ClassicalInvolution.Asc77.AscIHSectG
public import CFSG.ClassicalInvolution.AschTight.S1911P3a
public import CFSG.ClassicalInvolution.AschTight.S1911P3b
public import CFSG.ClassicalInvolution.AschTight.S1911SecG
public import CFSG.ClassicalInvolution.AschTight.S1916FusStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6FaField
public import CFSG.GH74.GLS.IVK.Lifted.GroupAux
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R1Prop46d
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.After
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements129b
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma58
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.LargeExtraspecial.Types
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.AS81GoldschmidtQO
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step25
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XTheorem4
public import CFSG.LocalAnalysis.ComponentClassification.GS82PumpInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSFMMaximal
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSteps
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitFrontier46
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKGFieldClass
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLit39b
public import CFSG.LocalAnalysis.ComponentInitial.FixedLayerNormalizes
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FunHypOmegaHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitLinearInner
public import CFSG.LocalAnalysis.UniquenessCase.UC22FunSplitPermutationAction
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aF
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.GoldschmidtRankOneUnitary
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.RankThree.SteinbergR3ELinearTwoOddFieldFixed

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.ClassicalInvolution.Models CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.StandardType
open scoped Pointwise

section Gen

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem iSup_coordBlockSU_card_three_eq_top (hK : Nat.card K = 4) {N : ℕ} (hN : 4 ≤ N) :
    (⨆ (I : Finset (Fin N)) (_ : I.card = 3), coordBlockSU K 2 1 I) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← fourBlockSup_eq_top hK hN]
  unfold fourBlockSup
  refine iSup₂_le fun I hI => ?_
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
  have hA : (I.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha]; omega
  have hB : (I.erase b).card = 3 := by rw [Finset.card_erase_of_mem hb]; omega
  have hU : I.erase a ∪ I.erase b = I := by
    ext x
    simp only [Finset.mem_union, Finset.mem_erase]
    constructor
    · rintro (h | h) <;> exact h.2
    · intro hx
      by_cases hxa : x = a
      · exact Or.inr ⟨fun h => hab (hxa ▸ h), hx⟩
      · exact Or.inl ⟨hxa, hx⟩
  have h4 := coordBlockSU_sup_three hK hA hB (by rw [hU, hI])
  rw [hU] at h4
  rw [← h4]
  exact sup_le (le_iSup₂_of_le (I.erase a) hA le_rfl) (le_iSup₂_of_le (I.erase b) hB le_rfl)

theorem range_eq_iSup_coordBlockSU_three {G : Type} [Group G] (hK : Nat.card K = 4) {N : ℕ}
    (hN : 4 ≤ N) (ψ : Su K 2 1 N →* G) :
    ψ.range = ⨆ (I : Finset (Fin N)) (_ : I.card = 3), (coordBlockSU K 2 1 I).map ψ := by
  rw [MonoidHom.range_eq_map, ← iSup_coordBlockSU_card_three_eq_top hK hN]
  simp only [Subgroup.map_iSup]

theorem coordBlockSU_mono {N : ℕ} {I I' : Finset (Fin N)} (h : I ⊆ I') :
    coordBlockSU K 2 1 I ≤ coordBlockSU K 2 1 I' := by
  intro g hg
  rw [mem_coordBlockSU_iff] at hg ⊢
  intro i j hij
  apply hg
  rcases hij with hi | hj
  · exact Or.inl fun hI => hi (h hI)
  · exact Or.inr fun hI => hj (h hI)

end Gen

end CFSG.StandardType.QTwo

end
