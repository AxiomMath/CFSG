module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetStab
public import CFSG.RankThree.PartOne.KE.E7FiveData
public import CFSG.ClassicalInvolution.Solomon73.YamakiPres
public import CFSG.Mathlib.Decide.Bounded
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LieType.Chevalley.OddTrialityCosetInvolutions
public import CFSG.LieType.Ree.LargeReeSylowOpposition
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedCosetDescent
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7E8NoninnerComponent
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.Basic
public import CFSG.RankThree.PartOne.KE.NativeCyclicMain
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open
open CFSG.OddStandard.SmallF3.Omega.E7RootSet
open CFSG.OddStandard.SmallF3.Omega
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Solomon73.Yamaki

theorem tmW7_rhoOmega_coe
    (w : evenWeyl) :
    ((rhoOmega w : omegaGroup e7QForm_nondegenerate) : _) = rho (w : WeylGroup Tag.E7) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  obtain ⟨v, rfl⟩ := redV_surj x
  rw [← toEq_eq_coe, toEq_rhoOmega, rho_apply_redV]
  exact rhoEquiv_redV _ _

theorem tmW7_evenWeyl_eq_ker :
    evenWeyl = (coxeterSystem Tag.E7).lengthParity.ker := by
  have hle : evenWeyl ≤ (coxeterSystem Tag.E7).lengthParity.ker := by
    intro w hw
    rw [MonoidHom.mem_ker]
    have h := (rhoOmega ⟨w, hw⟩).2
    rw [tmW7_rhoOmega_coe ⟨w, hw⟩] at h
    exact (rho_mem_omega_iff w).mp h
  have hW : Nat.card (WeylGroup Tag.E7) = 2903040 := by
    haveI : Fintype (WeylGroup Tag.E7) := Fintype.ofFinite _
    exact (CFSG.RankThree.Chevalley.E7_weyl_length_polynomial).2
  have hker_index : ((coxeterSystem Tag.E7).lengthParity.ker).index = 2 := by
    rw [Subgroup.index_ker, lengthParity_range, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcard : Nat.card ↥((coxeterSystem Tag.E7).lengthParity.ker) = 1451520 := by
    have h := Subgroup.card_mul_index ((coxeterSystem Tag.E7).lengthParity.ker)
    rw [hker_index, hW] at h
    omega
  have hcardle : Nat.card ↥((coxeterSystem Tag.E7).lengthParity.ker) ≤ Nat.card evenWeyl := by
    rw [hcard, natCard_evenWeyl]
  exact Subgroup.eq_of_le_of_card_ge hle hcardle

theorem tmW7_yamakiSp_02_ne :
    yamakiSp 0 * yamakiSp 2 ≠ yamakiSp 2 * yamakiSp 0 := by
  intro h
  have h1 : yamakiMat 0 * yamakiMat 2 = yamakiMat 2 * yamakiMat 0 := by
    have h' := congrArg spMat h
    rw [map_mul, map_mul] at h'
    have e0 : spMat (yamakiSp 0) = yamakiMat 0 := by
      change (((yamakiSp 0 : StatedSp 3 (ZMod 2)) : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = yamakiMat 0
      exact coe_yamakiSp 0
    have e2 : spMat (yamakiSp 2) = yamakiMat 2 := by
      change (((yamakiSp 2 : StatedSp 3 (ZMod 2)) : GL (Fin 3 ⊕ Fin 3) (ZMod 2)) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2)) = yamakiMat 2
      exact coe_yamakiSp 2
    rwa [e0, e2] at h'
  have h2 : ¬ (yamakiMat 0 * yamakiMat 2 = yamakiMat 2 * yamakiMat 0) := by decide +kernel
  exact h2 h1

theorem tmW7_not_isMulCommutative_sp62 :
    ¬ IsMulCommutative (StatedSp 3 (ZMod 2)) :=
  fun h => tmW7_yamakiSp_02_ne (h.is_comm.comm (yamakiSp 0) (yamakiSp 2))

end CFSG.StandardType.FrameRoute

end
