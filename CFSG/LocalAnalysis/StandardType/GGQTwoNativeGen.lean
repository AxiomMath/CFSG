module

public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapGen
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary Matrix

@[expose] noncomputable def fourBlockSup (K : Type) [Field K] [Finite K] [CharP K 2] (N : ℕ) :
    Subgroup (Su K 2 1 N) :=
  ⨆ (I : Finset (Fin N)) (_ : I.card = 4), coordBlockSU K 2 1 I

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private def qTwoNGB_ufd (hK : Nat.card K = 4) :
    CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
  ⟨Nat.prime_two, le_refl 1, by rw [hK]; norm_num⟩

private theorem qTwoNGB_card_eq (hK : Nat.card K = 4) : Nat.card K = ((2 : ℕ) ^ 1) ^ 2 := by
  rw [hK]; norm_num

private noncomputable def qTwoNGB_suEquiv (hK : Nat.card K = 4) (d : ℕ) :
    Su K 2 1 d ≃* CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K d :=
  MulEquiv.subgroupCongr
    (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU (p := 2) (f := 1) (qTwoNGB_card_eq hK) d)

private theorem qTwoNGB_coe_suEquiv_symm (hK : Nat.card K = 4) {d : ℕ}
    (x : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K d) :
    (((qTwoNGB_suEquiv hK d).symm x : Su K 2 1 d) : GL (Fin d) K) = (x : GL (Fin d) K) :=
  rfl

private theorem qTwoNGB_map_coordBlockSU (hK : Nat.card K = 4) (d : ℕ) (I : Finset (Fin d)) :
    (coordBlockSU K 2 1 I).map (qTwoNGB_suEquiv hK d).toMonoidHom =
      CFSG.SeitzReduction.UnitaryPilot.unitaryBlock (qTwoNGB_ufd hK) I := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_coordBlockSU_iff,
    CFSG.SeitzReduction.UnitaryPilot.mem_unitaryBlock]
  simp only [qTwoNGB_coe_suEquiv_symm, Matrix.one_apply]

private theorem qTwoNGB_card_I0 (M : ℕ) (hM : 3 ≤ M) :
    ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩} :
      Finset (Fin (M + 1))).card = 4 := by
  rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
    Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
    Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
    Finset.card_singleton]

theorem fourBlockSup_eq_top (hK : Nat.card K = 4) {N : ℕ} (hN : 4 ≤ N) : fourBlockSup K N = ⊤ := by
  have hUF := qTwoNGB_ufd hK
  have hgen := CFSG.SeitzReduction.UnitaryPilot.iSup_unitaryBlock_card_four_eq_top hUF hN
  have hmap : (fourBlockSup K N).map (qTwoNGB_suEquiv hK N).toMonoidHom = ⊤ := by
    apply le_antisymm le_top
    rw [← hgen]
    refine iSup₂_le fun I hI => ?_
    rw [← qTwoNGB_map_coordBlockSU hK N I]
    exact Subgroup.map_mono (le_iSup_of_le I (le_iSup_of_le hI le_rfl))
  rw [eq_top_iff]
  intro g _
  have hg : qTwoNGB_suEquiv hK N g ∈
      (fourBlockSup K N).map (qTwoNGB_suEquiv hK N).toMonoidHom := by
    rw [hmap]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hg
  exact hg

theorem eq_top_of_fourBlock_of_swaps (hK : Nat.card K = 4) {N : ℕ} (hN : 4 ≤ N) (H : Subgroup (Su K 2 1 N))
    (hblk : coordBlockSU K 2 1 ({⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩} : Finset (Fin N)) ≤ H)
    (hswap : ∀ i j : Fin N, i.val + 1 = j.val → ∀ g : Su K 2 1 N,
      (((g : Su K 2 1 N) : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = (Equiv.swap i j).permMatrix K → g ∈ H) :
    H = ⊤ := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hUF := qTwoNGB_ufd hK
  set I₀ : Finset (Fin (M + 1)) :=
    {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩} with hI₀
  have hI₀card : I₀.card = 4 := by rw [hI₀]; exact qTwoNGB_card_I0 M (by omega)
  set H' : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 K (M + 1)) :=
    H.map (qTwoNGB_suEquiv hK (M + 1)).toMonoidHom with hH'
  have hblk' : CFSG.SeitzReduction.UnitaryPilot.unitaryBlock hUF I₀ ≤ H' := by
    rw [← qTwoNGB_map_coordBlockSU hK (M + 1) I₀]
    exact Subgroup.map_mono hblk
  have hperm : ∀ σ : Equiv.Perm (Fin (M + 1)),
      CFSG.SeitzReduction.UnitaryPilot.permSU hUF σ ∈ H' := by
    have hle : Submonoid.closure
        (Set.range fun k : Fin M => Equiv.swap k.castSucc k.succ) ≤
        (H'.comap (CFSG.SeitzReduction.UnitaryPilot.permSUHom hUF)).toSubmonoid := by
      rw [Submonoid.closure_le]
      rintro _ ⟨k, rfl⟩
      show CFSG.SeitzReduction.UnitaryPilot.permSUHom hUF (Equiv.swap k.castSucc k.succ) ∈ H'
      rw [CFSG.SeitzReduction.UnitaryPilot.permSUHom_apply, Equiv.swap_inv]
      rw [hH', Subgroup.mem_map_equiv]
      apply hswap k.castSucc k.succ
      · simp
      · rw [qTwoNGB_coe_suEquiv_symm, CFSG.SeitzReduction.UnitaryPilot.coe_permSU]
    rw [Equiv.Perm.mclosure_swap_castSucc_succ] at hle
    intro σ
    have hσ : σ⁻¹ ∈ H'.comap (CFSG.SeitzReduction.UnitaryPilot.permSUHom hUF) :=
      hle (Submonoid.mem_top σ⁻¹)
    rw [Subgroup.mem_comap, CFSG.SeitzReduction.UnitaryPilot.permSUHom_apply, inv_inv] at hσ
    exact hσ
  have huni : ∀ J : Finset (Fin (M + 1)), J.card = 4 →
      CFSG.SeitzReduction.UnitaryPilot.unitaryBlock hUF J ≤ H' := by
    intro J hJ
    exact CFSG.SeitzReduction.UnitaryPilot.unitaryBlock_le_of_permSU_mem hUF hperm
      (by rw [hI₀card, hJ]) hblk'
  have hH'top : H' = ⊤ := by
    rw [eq_top_iff, ← CFSG.SeitzReduction.UnitaryPilot.iSup_unitaryBlock_card_four_eq_top hUF hN]
    exact iSup₂_le fun J hJ => huni J hJ
  rw [eq_top_iff]
  intro g _
  have hg : qTwoNGB_suEquiv hK (M + 1) g ∈ H' := by
    rw [hH'top]
    exact Subgroup.mem_top _
  rw [hH', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hg
  exact hg

end CFSG.StandardType.QTwo

end
