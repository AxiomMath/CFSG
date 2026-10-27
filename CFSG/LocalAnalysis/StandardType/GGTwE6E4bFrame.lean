module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FixedA2SL3
import CFSG.HardMathSupport.Solomon.LocalBalance.GlueTools
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralBlocks
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.Mathlib.RingTheory.UnitOrderOf
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadSingerFrame
public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddNeThree
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.Final
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTorusGen
public import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagTorus
public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
public import CFSG.LieType.SeitzGeneration.OuterSpPair
public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
public import CFSG.LieType.SeitzGeneration.RootPairSp
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCyc
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotUniqueField
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.RankThree.PartOne.Census3.Assembly
public import CFSG.RankThree.PartOne.FOC.Cases
public import CFSG.RankThree.PartOne.FOC.CompEquiv
public import CFSG.RankThree.PartOne.FOC.PSLFamily
public import CFSG.RankThree.PartOne.FOC.PSLLie
public import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
public import CFSG.RankThree.PartOne.FOCD.PRank
public import CFSG.RankThree.PartOne.KC.UnitaryDefining
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartOne.SEITZ11.G2OddFinal
public import CFSG.RankThree.PartOne.SEITZ7.D4Wire
public import CFSG.RankThree.PartOne.SEITZ7.SzPairK
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofExc
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec4
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzSz
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import Certificates.Certificate16005
public import Certificates.Certificate3044
public import Certificates.Certificate3122
public import Certificates.Certificate3123
public import Certificates.Certificate3130
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3179
public import Certificates.Certificate8160

public noncomputable section

namespace CFSG.StandardType.TwE6E4bFrame

open scoped MatrixGroups
open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.Three
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6NonToralThree
  CFSG.StandardType.E6ThreeEnd CFSG.StandardType.TwE6HyperplaneTypes
  CFSG.StandardType.TwE6FixedA2Type CFSG.StandardType.TwE6FixedA2SL3
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.TCX.E
  CFSG.RankThree.E6 CFSG.RankThree.PartOne.KD4T CFSG.LieType.Steinberg.Adjoint

local instance e4bFrameNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def frameR0 : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 1, 1, 1]

@[expose] def frameR2 : Fin Tag.E6.rank → ℤ := ![1, 0, 1, 1, 1, 0]

@[expose] def frameWord1 : List (Fin Tag.E6.rank) := [5, 2, 1, 3, 4, 2, 1, 3]

@[expose] def frameWord2 : List (Fin Tag.E6.rank) := [4, 5, 0, 2, 1, 3, 4, 3, 0, 2, 1, 3]

@[expose] def frameV1 : WeylGroup Tag.E6 := (coxeterSystem .E6).wordProd frameWord1

@[expose] def frameV2 : WeylGroup Tag.E6 := (coxeterSystem .E6).wordProd frameWord2

end CFSG.StandardType.TwE6E4bFrame

namespace CFSG.StandardType.TwE6E4bFrame

open scoped MatrixGroups
open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.Three
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6NonToralThree
  CFSG.StandardType.E6ThreeEnd CFSG.StandardType.TwE6HyperplaneTypes
  CFSG.StandardType.TwE6FixedA2Type CFSG.StandardType.TwE6FixedA2SL3
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.TCX.E
  CFSG.RankThree.E6 CFSG.RankThree.PartOne.KD4T CFSG.LieType.Steinberg.Adjoint

@[expose] def frameRho0 (L : Type) [Field L] : SL(3, L) →* ModGL Tag.E6 L :=
  fixedA2Rho L

@[expose] def frameRho1 (L : Type) [Field L] : SL(3, L) →* ModGL Tag.E6 L :=
  a2Std₁.rhoV L frameV1

@[expose] def frameRho2 (L : Type) [Field L] : SL(3, L) →* ModGL Tag.E6 L :=
  a2Std₁.rhoV L frameV2

end CFSG.StandardType.TwE6E4bFrame

namespace CFSG.StandardType.TwE6E4bFrame

open scoped MatrixGroups
open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.Three
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6NonToralThree
  CFSG.StandardType.E6ThreeEnd CFSG.StandardType.TwE6HyperplaneTypes
  CFSG.StandardType.TwE6FixedA2Type CFSG.StandardType.TwE6FixedA2SL3
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.TCX.E
  CFSG.RankThree.E6 CFSG.RankThree.PartOne.KD4T CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

@[expose] def frameQ (L : Type) [Field L] (A B C : SL(3, L)) : ModGL Tag.E6 L :=
  frameRho0 L A * frameRho1 L B * frameRho2 L C

end CFSG.StandardType.TwE6E4bFrame

namespace CFSG.StandardType.TwE6E4bFrame

open scoped MatrixGroups
open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc.Three
  CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6NonToralThree
  CFSG.StandardType.E6ThreeEnd CFSG.StandardType.TwE6HyperplaneTypes
  CFSG.StandardType.TwE6FixedA2Type CFSG.StandardType.TwE6FixedA2SL3
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.TCX.E
  CFSG.RankThree.E6 CFSG.RankThree.PartOne.KD4T CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

section Torsion

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem exists_frameOmega : ∃ ω : Lˣ, orderOf ω = 3 := by
  refine CFSG.exists_unit_orderOf_eq_of_isAlgClosed (n := 3) ?_
  have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
  change (OfNat.ofNat 3 : L) ≠ 0
  rw [show (OfNat.ofNat 3 : L) = 2 + 1 by norm_num, h2, zero_add]
  exact one_ne_zero

noncomputable def frameOmega : Lˣ := Classical.choose (exists_frameOmega (L := L))

theorem frameOmega_orderOf : orderOf (frameOmega (L := L)) = 3 :=
  Classical.choose_spec (exists_frameOmega (L := L))

theorem frameOmega_pow_three : (frameOmega (L := L)) ^ 3 = 1 := by
  rw [← frameOmega_orderOf (L := L)]
  exact pow_orderOf_eq_one _

theorem frameOmega_ne_one : frameOmega (L := L) ≠ 1 := by
  intro h
  have h3 := frameOmega_orderOf (L := L)
  rw [h, orderOf_one] at h3
  exact (by norm_num : (1 : ℕ) ≠ 3) h3

@[expose] def frameBeta : SL(3, L) :=
  diagSL3 1 (frameOmega (L := L))

@[expose] def frameScalar : SL(3, L) :=
  diagSL3 (frameOmega (L := L)) ((frameOmega (L := L)) ^ 2)

@[expose] def frameA : ModGL Tag.E6 L :=
  frameQ L (frameScalar (L := L)) 1 1

@[expose] def frameT : ModGL Tag.E6 L :=
  frameQ L (frameBeta (L := L)) 1 1

@[expose] def frameX : ModGL Tag.E6 L :=
  frameQ L 1 (frameBeta (L := L)) (frameBeta (L := L))

theorem frameA_eq : frameA (L := L) = frameRho0 L (frameScalar (L := L)) := by
  simp [frameA, frameQ]

theorem frameT_eq : frameT (L := L) = frameRho0 L (frameBeta (L := L)) := by
  simp [frameT, frameQ]

theorem frameX_eq : frameX (L := L) = frameRho1 L (frameBeta (L := L)) *
    frameRho2 L (frameBeta (L := L)) := by
  simp [frameX, frameQ]

theorem frameRho1_diag_mem_torus {A : SL(3, L)}
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    frameRho1 L A ∈ torusGroup Tag.E6 L :=
  (a2Std₁.embedding frameV1).diag L A hA

theorem frameRho2_diag_mem_torus {A : SL(3, L)}
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) L) i j = 0) :
    frameRho2 L A ∈ torusGroup Tag.E6 L :=
  (a2Std₁.embedding frameV2).diag L A hA

theorem frameA_mem_torus : frameA (L := L) ∈ torusGroup Tag.E6 L := by
  rw [frameA_eq]
  exact fixedA2Rho_diag_mem_torusGroup L _
    (fun i j hij => diagSL3_apply_ne _ _ hij)

theorem frameT_mem_torus : frameT (L := L) ∈ torusGroup Tag.E6 L := by
  rw [frameT_eq]
  exact fixedA2Rho_diag_mem_torusGroup L _
    (fun i j hij => diagSL3_apply_ne _ _ hij)

theorem frameX_mem_torus : frameX (L := L) ∈ torusGroup Tag.E6 L := by
  rw [frameX_eq]
  exact mul_mem
    (frameRho1_diag_mem_torus (L := L) (fun i j hij => diagSL3_apply_ne _ _ hij))
    (frameRho2_diag_mem_torus (L := L) (fun i j hij => diagSL3_apply_ne _ _ hij))

theorem frameT_weylQuotientHom :
    weylQuotientHom .E6 L
        ⟨frameT (L := L), torusGroup_le_monomialSubgroup (frameT_mem_torus (L := L))⟩ = 1 :=
  weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup (frameT_mem_torus (L := L)))

def frameFixedA2ActionVec : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![0, 1, 0, 1, 1, 0], ![0, 0, 1, 1, 1, 0], ![-1, -1, -1, -2, -1, 0],
    ![1, 0, 0, 0, 0, 0], ![0, 1, 1, 1, 0, 0], ![0, 0, 0, 1, 1, 1]]

set_option maxRecDepth 1000000 in
theorem frameFixedA2V_inv_smul_single (j : Fin Tag.E6.rank) :
    (fixedA2V⁻¹ • (Pi.single j (1 : ℤ) : Fin Tag.E6.rank → ℤ) :
      Fin Tag.E6.rank → ℤ) = frameFixedA2ActionVec j := by
  rw [fixedA2V, ← CoxeterSystem.wordProd_reverse, CFSG.LieType.Chevalley.wordProd_smul]
  revert j
  decide +kernel

set_option maxRecDepth 1000000 in
set_option backward.isDefEq.respectTransparency false in
theorem frameDiagTuple_explicit {L : Type} [Field L] (s u : Lˣ) :
    diagTuple s u = ![u⁻¹, s⁻¹ * u, s⁻¹ * u, s ^ 2 * u⁻¹, s⁻¹ * u, u⁻¹] := by
  classical
  change (fun j : Fin 6 => diagTuple s u j) =
    (![u⁻¹, s⁻¹ * u, s⁻¹ * u, s ^ 2 * u⁻¹, s⁻¹ * u, u⁻¹] : Fin 6 → Lˣ)
  funext j
  rw [diagTuple, weylTuple, frameFixedA2V_inv_smul_single]
  change (∏ i : Fin 6, (s ^ Tag.E6.cartan 0 i * u ^ Tag.E6.cartan 2 i) ^
    frameFixedA2ActionVec j i) = _
  simp only [Fin.prod_univ_succ]
  fin_cases j <;> norm_num [Tag.cartan, Tag.cartanE, frameFixedA2ActionVec]
  all_goals ext <;> simp <;> field_simp <;> ring

def frameExpA : Fin Tag.E6.rank → ℤ := ![1, 1, 1, 0, 1, 1]

def frameExpT : Fin Tag.E6.rank → ℤ := ![2, 1, 1, 2, 1, 2]

def frameExpX : Fin Tag.E6.rank → ℤ := ![0, 1, 1, 0, 1, 0]

noncomputable def frameTorusTuple (e : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → Lˣ :=
  fun i => frameOmega ^ e i

theorem frameTorusTuple_frameExpX_values :
    frameTorusTuple (L := L) frameExpX (1 : Fin Tag.E6.rank) = frameOmega (L := L) ∧
    frameTorusTuple (L := L) frameExpX (2 : Fin Tag.E6.rank) = frameOmega (L := L) ∧
    frameTorusTuple (L := L) frameExpX (3 : Fin Tag.E6.rank) = 1 ∧
    frameTorusTuple (L := L) frameExpX (4 : Fin Tag.E6.rank) = frameOmega (L := L) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [frameTorusTuple, frameExpX]

theorem frameOmega_mul_sq : frameOmega (L := L) * frameOmega ^ 2 = 1 := by
  calc frameOmega (L := L) * frameOmega ^ 2 = frameOmega ^ 1 * frameOmega ^ 2 := by rw [pow_one]
    _ = frameOmega ^ (1 + 2) := (pow_add _ _ _).symm
    _ = frameOmega ^ 3 := by norm_num
    _ = 1 := frameOmega_pow_three

theorem frameOmega_sq_mul : frameOmega (L := L) ^ 2 * frameOmega = 1 := by
  calc frameOmega (L := L) ^ 2 * frameOmega = frameOmega ^ 2 * frameOmega ^ 1 := by rw [pow_one]
    _ = frameOmega ^ (2 + 1) := (pow_add _ _ _).symm
    _ = frameOmega ^ 3 := by norm_num
    _ = 1 := frameOmega_pow_three

theorem frameOmega_sq_mul_sq : frameOmega (L := L) ^ 2 * frameOmega ^ 2 = frameOmega := by
  calc frameOmega (L := L) ^ 2 * frameOmega ^ 2 = frameOmega ^ (2 + 2) := (pow_add _ _ _).symm
    _ = frameOmega ^ 4 := by norm_num
    _ = frameOmega ^ (3 + 1) := by norm_num
    _ = frameOmega ^ 3 * frameOmega := by simpa using pow_add (frameOmega (L := L)) 3 1
    _ = frameOmega := by rw [frameOmega_pow_three, one_mul]

theorem frameOmega_inv : (frameOmega (L := L))⁻¹ = frameOmega ^ 2 :=
  inv_eq_of_mul_eq_one_right frameOmega_mul_sq

theorem frameOmega_sq_inv : ((frameOmega (L := L)) ^ 2)⁻¹ = frameOmega :=
  inv_eq_of_mul_eq_one_right frameOmega_sq_mul

theorem frameA_eq_rootDiagUnit :
    frameA (L := L) = rootDiagUnit Tag.E6 (frameTorusTuple (L := L) frameExpA) := by
  rw [frameA_eq, frameRho0]
  change fixedA2Rho L (diagSL3 (frameOmega (L := L)) ((frameOmega (L := L)) ^ 2)) = _
  rw [fixedA2Rho_diagSL3, frameDiagTuple_explicit]
  congr 1
  funext i
  fin_cases i <;>
    simp [frameScalar, diagSL3, frameTorusTuple, frameExpA, frameOmega_inv,
      frameOmega_sq_inv, frameOmega_sq_mul_sq, frameOmega_sq_mul,
      Units.val_inv_eq_inv_val]

theorem frameT_eq_rootDiagUnit :
    frameT (L := L) = rootDiagUnit Tag.E6 (frameTorusTuple (L := L) frameExpT) := by
  rw [frameT_eq, frameRho0]
  change fixedA2Rho L (diagSL3 1 (frameOmega (L := L))) = _
  rw [fixedA2Rho_diagSL3, frameDiagTuple_explicit]
  congr 1
  funext i
  fin_cases i <;>
    simp [frameBeta, diagSL3, frameTorusTuple, frameExpT, frameOmega_inv,
      frameOmega_sq_inv, frameOmega_sq_mul_sq, frameOmega_sq_mul,
      Units.val_inv_eq_inv_val]

theorem a2Equiv₁_e6TorusPair (s u : Lˣ) :
    a2Equiv₁ L ⟨e6TorusPair (e6Index 0) (e6Index 2) s u,
      e6TorusPair_mem_subsystemGroup _ _ s u⟩ = diagSL3 s u := by
  rw [a2Equiv₁_apply]
  apply Subtype.ext
  rw [coe_a2Rep₁]
  change a2Mat₁ (e6TorusPair (e6Index 0) (e6Index 2) s u) =
    ((diagSL3 s u : SL(3, L)) : Matrix (Fin 3) (Fin 3) L)
  rw [a2Mat₁_torus]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSL3, Matrix.diagonal_apply]

theorem e6rhoA2₁_diagSL3 (s u : Lˣ) :
    e6rhoA2₁ L (diagSL3 s u) =
      e6TorusPair (e6Index 0) (e6Index 2) s u := by
  have hmem : e6TorusPair (e6Index 0) (e6Index 2) s u ∈
      subsystemGroup Tag.E6 L support13 :=
    e6TorusPair_mem_subsystemGroup _ _ s u
  have h := a2Equiv₁_e6TorusPair (L := L) s u
  have h' : (a2Equiv₁ L).symm (diagSL3 s u) =
      ⟨e6TorusPair (e6Index 0) (e6Index 2) s u, hmem⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact h.symm
  rw [e6rhoA2₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  exact congrArg Subtype.val h'

theorem frameBeta_e6rho :
    e6rhoA2₁ L (frameBeta (L := L)) =
      rootDiagUnit Tag.E6 (fun j => frameOmega ^ Tag.E6.cartan 2 j) := by
  rw [frameBeta, e6rhoA2₁_diagSL3]
  rw [show e6TorusPair (e6Index 0) (e6Index 2) (1 : Lˣ) (frameOmega (L := L)) =
      torusElt Tag.E6 L (e6Index 2) (frameOmega (L := L)) by
    rw [e6TorusPair, torusElt_one, one_mul]]
  exact torusElt_eq_rootDiagUnit (e6Index 2) (frameOmega (L := L))

def frameV1InvSingle : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![1, 1, 1, 2, 1, 0], ![0, 0, -1, -1, -1, 0], ![0, -1, 0, -1, -1, 0],
    ![0, 0, 0, 0, 1, 0], ![0, 1, 1, 2, 1, 1], ![0, 0, 0, -1, -1, -1]]

def frameV2InvSingle : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![0, -1, 0, -1, -1, 0], ![0, 0, -1, -1, -1, 0], ![-1, 0, -1, -1, 0, 0],
    ![1, 1, 2, 3, 2, 1], ![0, 0, 0, -1, -1, -1], ![0, -1, -1, -1, 0, 0]]

theorem frameV1_inv_smul_single (i : Fin Tag.E6.rank) :
    (frameV1⁻¹ • (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) :
      Fin Tag.E6.rank → ℤ) = frameV1InvSingle i := by
  have h1 : frameV1⁻¹ = (coxeterSystem .E6).wordProd frameWord1.reverse := by
    rw [frameV1, CoxeterSystem.wordProd_reverse]
  rw [h1, CFSG.LieType.Chevalley.wordProd_smul]
  funext j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem frameV2_inv_smul_single (i : Fin Tag.E6.rank) :
    (frameV2⁻¹ • (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) :
      Fin Tag.E6.rank → ℤ) = frameV2InvSingle i := by
  have h1 : frameV2⁻¹ = (coxeterSystem .E6).wordProd frameWord2.reverse := by
    rw [frameV2, CoxeterSystem.wordProd_reverse]
  rw [h1, CFSG.LieType.Chevalley.wordProd_smul]
  funext j
  fin_cases i <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 1000000 in
theorem frameV1_weylTuple_cartan :
    weylTuple frameV1 (fun j => (frameOmega (L := L)) ^ Tag.E6.cartan 2 j) =
      fun i => frameOmega ^ (∑ j, Tag.E6.cartan i j * (frameR0 j)) := by
  funext i
  rw [weylTuple, rootChar, frameV1_inv_smul_single i]
  simp only [← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  congr 1
  fin_cases i <;> decide +kernel

set_option maxRecDepth 1000000 in
theorem frameV2_weylTuple_cartan :
    weylTuple frameV2 (fun j => (frameOmega (L := L)) ^ Tag.E6.cartan 2 j) =
      fun i => frameOmega ^ (∑ j, Tag.E6.cartan i j * (frameR2 j)) := by
  funext i
  rw [weylTuple, rootChar, frameV2_inv_smul_single i]
  simp only [← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  congr 1
  fin_cases i <;> decide +kernel

theorem frameRho1_beta :
    frameRho1 L (frameBeta (L := L)) =
      rootDiagUnit Tag.E6 (weylTuple frameV1
        (fun j => (frameOmega (L := L)) ^ Tag.E6.cartan 2 j)) := by
  rw [frameRho1, A2Std.rhoV, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  change canonicalRep (coxeterSystem .E6) L frameV1 * e6rhoA2₁ L (frameBeta (L := L)) *
      (canonicalRep (coxeterSystem .E6) L frameV1)⁻¹ = _
  rw [frameBeta_e6rho, canonicalRep_conj_rootDiagUnit]

theorem frameRho2_beta :
    frameRho2 L (frameBeta (L := L)) =
      rootDiagUnit Tag.E6 (weylTuple frameV2
        (fun j => (frameOmega (L := L)) ^ Tag.E6.cartan 2 j)) := by
  rw [frameRho2, A2Std.rhoV, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  change canonicalRep (coxeterSystem .E6) L frameV2 * e6rhoA2₁ L (frameBeta (L := L)) *
      (canonicalRep (coxeterSystem .E6) L frameV2)⁻¹ = _
  rw [frameBeta_e6rho, canonicalRep_conj_rootDiagUnit]

theorem frameOmega_zpow_neg_two :
    (frameOmega (L := L)) ^ (-2 : ℤ) = frameOmega := by
  rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg]
  exact frameOmega_sq_inv (L := L)

set_option maxRecDepth 1000000 in
theorem frameX_eq_rootDiagUnit :
    frameX (L := L) = rootDiagUnit Tag.E6 (frameTorusTuple (L := L) frameExpX) := by
  rw [frameX_eq, frameRho1_beta, frameRho2_beta, ← rootDiagUnit_mul,
    frameV1_weylTuple_cartan, frameV2_weylTuple_cartan]
  congr 1
  funext i
  simp only [Pi.mul_apply, frameTorusTuple]
  rw [← zpow_add]
  fin_cases i
  · rfl
  · change frameOmega ^ (∑ j : Fin Tag.E6.rank, Tag.E6.cartan 1 j * frameR0 j +
        ∑ j : Fin Tag.E6.rank, Tag.E6.cartan 1 j * frameR2 j) =
      frameOmega ^ frameExpX 1
    rw [show (∑ j : Fin Tag.E6.rank, Tag.E6.cartan 1 j * frameR0 j +
        ∑ j : Fin Tag.E6.rank, Tag.E6.cartan 1 j * frameR2 j) = -2 by
      decide +kernel]
    rw [frameOmega_zpow_neg_two]
    rw [show frameExpX 1 = 1 by decide, zpow_one]
  · rfl
  · rfl
  · rfl
  · rfl

def frameCInvSingle : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![-1, -2, -2, -3, -2, -1], ![0, 0, 0, 0, 1, 0], ![0, 1, 0, 0, 0, 0],
    ![0, 0, 0, 1, 0, 0], ![0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 0]]

theorem cE6_inv_smul_single (i : Fin Tag.E6.rank) :
    (cE6⁻¹ • (Pi.single i (1 : ℤ) : Fin Tag.E6.rank → ℤ) :
      Fin Tag.E6.rank → ℤ) = frameCInvSingle i := by
  have h : cE6⁻¹ = (coxeterSystem .E6).wordProd wordE6C.reverse := by
    rw [cE6, CoxeterSystem.wordProd_reverse]
  rw [h, CFSG.LieType.Chevalley.wordProd_smul]
  funext j
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem weylTuple_cE6_apply (b : Fin Tag.E6.rank → Lˣ) (i : Fin Tag.E6.rank) :
    weylTuple cE6 b i = rootChar b (frameCInvSingle i) := by
  rw [weylTuple, cE6_inv_smul_single]

theorem weylTuple_cE6_eq_imp (b : Fin Tag.E6.rank → Lˣ)
    (h : weylTuple cE6 b = b) :
    b 0 = b 5 ∧ b 1 = b 2 ∧ b 2 = b 4 := by
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  rw [weylTuple_cE6_apply] at h1 h2 h4 h5
  rw [show frameCInvSingle 1 = (Pi.single 4 (1:ℤ) : Fin Tag.E6.rank → ℤ) by decide,
    rootChar_single] at h1
  rw [show frameCInvSingle 2 = (Pi.single 1 (1:ℤ) : Fin Tag.E6.rank → ℤ) by decide,
    rootChar_single] at h2
  rw [show frameCInvSingle 4 = (Pi.single 2 (1:ℤ) : Fin Tag.E6.rank → ℤ) by decide,
    rootChar_single] at h4
  rw [show frameCInvSingle 5 = (Pi.single 0 (1:ℤ) : Fin Tag.E6.rank → ℤ) by decide,
    rootChar_single] at h5
  exact ⟨h5, h2, h4⟩

theorem exists_fin3_eq_frameOmega_zpow (x : Lˣ) (hx : x ^ 3 = 1) :
    ∃ r : Fin 3, x = (frameOmega (L := L)) ^ (r : ℕ) := by
  have hprimL : IsPrimitiveRoot (frameOmega (L := L) : L) 3 := by
    have h := IsPrimitiveRoot.orderOf (frameOmega (L := L) : L)
    rwa [orderOf_units, frameOmega_orderOf] at h
  have hxL : (x : L) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  obtain ⟨i, hi, hix⟩ := hprimL.eq_pow_of_pow_eq_one hxL
  refine ⟨⟨i, hi⟩, ?_⟩
  apply Units.ext
  simpa using hix.symm

theorem frameOmega_zpow_eq_of_eq_add_three_mul {a b m : ℤ}
    (h : a = b + 3 * m) :
    (frameOmega (L := L)) ^ a = (frameOmega (L := L)) ^ b := by
  rw [h, zpow_add]
  have hbase : (frameOmega (L := L)) ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact frameOmega_pow_three (L := L)
  have h3 : (frameOmega (L := L)) ^ (3 * m) = 1 := by
    rw [zpow_mul, hbase, one_zpow]
  rw [h3, mul_one]

@[expose] noncomputable def frameD : Subgroup (ModGL Tag.E6 L) :=
  Subgroup.closure ({frameA (L := L), frameT (L := L), frameX (L := L)} :
    Set (ModGL Tag.E6 L))

theorem frameCToralTuple_mem_frameD (b : Fin Tag.E6.rank → Lˣ)
    (hb : ∀ i, b i ^ 3 = 1)
    (h05 : b 0 = b 5) (h12 : b 1 = b 2) (h24 : b 2 = b 4) :
    rootDiagUnit Tag.E6 b ∈ frameD := by
  obtain ⟨r, hr⟩ := exists_fin3_eq_frameOmega_zpow (b 0) (hb 0)
  obtain ⟨s, hs⟩ := exists_fin3_eq_frameOmega_zpow (b 1) (hb 1)
  obtain ⟨t, ht⟩ := exists_fin3_eq_frameOmega_zpow (b 3) (hb 3)
  let i : ℤ := (r : ℤ) - (t : ℤ)
  let j : ℤ := 2 * (t : ℤ)
  let k : ℤ := (s : ℤ) - (r : ℤ) - (t : ℤ)
  have hbprod : b = fun l => (frameOmega (L := L)) ^
      (i * frameExpA l + j * frameExpT l + k * frameExpX l) := by
    funext l
    fin_cases l
    · change b 0 = (frameOmega (L := L)) ^
          (i * frameExpA 0 + j * frameExpT 0 + k * frameExpX 0)
      have h0 : i * frameExpA 0 + j * frameExpT 0 + k * frameExpX 0 =
          (r : ℤ) + 3 * (t : ℤ) := by
        simp [i, j, frameExpA, frameExpT, frameExpX]
        ring_nf
      rw [hr, ← zpow_natCast, h0]
      exact (frameOmega_zpow_eq_of_eq_add_three_mul
        (a := (r : ℤ) + 3 * (t : ℤ)) (b := (r : ℤ)) (m := (t : ℤ)) (by ring)).symm
    · change b 1 = (frameOmega (L := L)) ^
          (i * frameExpA 1 + j * frameExpT 1 + k * frameExpX 1)
      have h1 : i * frameExpA 1 + j * frameExpT 1 + k * frameExpX 1 =
          (s : ℤ) := by
        simp [i, j, k, frameExpA, frameExpT, frameExpX]
        ring_nf
      rw [hs, ← zpow_natCast, h1]
    · change b 2 = (frameOmega (L := L)) ^
          (i * frameExpA 2 + j * frameExpT 2 + k * frameExpX 2)
      have h2 : i * frameExpA 2 + j * frameExpT 2 + k * frameExpX 2 =
          (s : ℤ) := by
        simp [i, j, k, frameExpA, frameExpT, frameExpX]
        ring_nf
      rw [← h12, hs, ← zpow_natCast, h2]
    · change b 3 = (frameOmega (L := L)) ^
          (i * frameExpA 3 + j * frameExpT 3 + k * frameExpX 3)
      have h3 : i * frameExpA 3 + j * frameExpT 3 + k * frameExpX 3 =
          (t : ℤ) + 3 * (t : ℤ) := by
        simp [i, j, frameExpA, frameExpT, frameExpX]
        ring_nf
      rw [ht, ← zpow_natCast, h3]
      exact (frameOmega_zpow_eq_of_eq_add_three_mul
        (a := (t : ℤ) + 3 * (t : ℤ)) (b := (t : ℤ)) (m := (t : ℤ)) (by ring)).symm
    · change b 4 = (frameOmega (L := L)) ^
          (i * frameExpA 4 + j * frameExpT 4 + k * frameExpX 4)
      have h4 : i * frameExpA 4 + j * frameExpT 4 + k * frameExpX 4 =
          (s : ℤ) := by
        simp [i, j, k, frameExpA, frameExpT, frameExpX]
        ring_nf
      rw [← h24, ← h12, hs, ← zpow_natCast, h4]
    · change b 5 = (frameOmega (L := L)) ^
          (i * frameExpA 5 + j * frameExpT 5 + k * frameExpX 5)
      have h5 : i * frameExpA 5 + j * frameExpT 5 + k * frameExpX 5 =
          (r : ℤ) + 3 * (t : ℤ) := by
        simp [i, j, frameExpA, frameExpT, frameExpX]
        ring_nf
      rw [← h05, hr, ← zpow_natCast, h5]
      exact (frameOmega_zpow_eq_of_eq_add_three_mul
        (a := (r : ℤ) + 3 * (t : ℤ)) (b := (r : ℤ)) (m := (t : ℤ)) (by ring)).symm
  have hA_hom : frameA (L := L) =
      rootDiagUnitHom Tag.E6 L (frameTorusTuple frameExpA) := by
    rw [frameA_eq_rootDiagUnit]; rfl
  have hT_hom : frameT (L := L) =
      rootDiagUnitHom Tag.E6 L (frameTorusTuple frameExpT) := by
    rw [frameT_eq_rootDiagUnit]; rfl
  have hX_hom : frameX (L := L) =
      rootDiagUnitHom Tag.E6 L (frameTorusTuple frameExpX) := by
    rw [frameX_eq_rootDiagUnit]; rfl
  have hpowA : frameA ^ i = rootDiagUnit Tag.E6
      (fun l => (frameOmega (L := L)) ^ (i * frameExpA l)) := by
    rw [hA_hom, ← map_zpow (rootDiagUnitHom Tag.E6 L)]
    change (rootDiagUnitHom Tag.E6 L) (frameTorusTuple frameExpA ^ i) =
      (rootDiagUnitHom Tag.E6 L)
        (fun l => (frameOmega (L := L)) ^ (i * frameExpA l))
    congr 1
    funext l
    simp only [Pi.pow_apply, frameTorusTuple]
    rw [← zpow_mul, mul_comm]
  have hpowT : frameT ^ j = rootDiagUnit Tag.E6
      (fun l => (frameOmega (L := L)) ^ (j * frameExpT l)) := by
    rw [hT_hom, ← map_zpow (rootDiagUnitHom Tag.E6 L)]
    change (rootDiagUnitHom Tag.E6 L) (frameTorusTuple frameExpT ^ j) =
      (rootDiagUnitHom Tag.E6 L)
        (fun l => (frameOmega (L := L)) ^ (j * frameExpT l))
    congr 1
    funext l
    simp only [Pi.pow_apply, frameTorusTuple]
    rw [← zpow_mul, mul_comm]
  have hpowX : frameX ^ k = rootDiagUnit Tag.E6
      (fun l => (frameOmega (L := L)) ^ (k * frameExpX l)) := by
    rw [hX_hom, ← map_zpow (rootDiagUnitHom Tag.E6 L)]
    change (rootDiagUnitHom Tag.E6 L) (frameTorusTuple frameExpX ^ k) =
      (rootDiagUnitHom Tag.E6 L)
        (fun l => (frameOmega (L := L)) ^ (k * frameExpX l))
    congr 1
    funext l
    simp only [Pi.pow_apply, frameTorusTuple]
    rw [← zpow_mul, mul_comm]
  have hsplit : (fun l => (frameOmega (L := L)) ^
        (i * frameExpA l + j * frameExpT l + k * frameExpX l)) =
      (fun l => (frameOmega (L := L)) ^ (i * frameExpA l)) *
        (fun l => (frameOmega (L := L)) ^ (j * frameExpT l)) *
        (fun l => (frameOmega (L := L)) ^ (k * frameExpX l)) := by
    funext l
    simp only [Pi.mul_apply]
    rw [← zpow_add, ← zpow_add]
  have hEq : rootDiagUnit Tag.E6 b = frameA ^ i * frameT ^ j * frameX ^ k := by
    rw [hbprod, hsplit, rootDiagUnit_mul, rootDiagUnit_mul, hpowA, hpowT, hpowX]
  have hA : frameA (L := L) ∈
      ({frameA (L := L), frameT (L := L), frameX (L := L)} : Set (ModGL Tag.E6 L)) := by simp
  have hT : frameT (L := L) ∈
      ({frameA (L := L), frameT (L := L), frameX (L := L)} : Set (ModGL Tag.E6 L)) := by simp
  have hX : frameX (L := L) ∈
      ({frameA (L := L), frameT (L := L), frameX (L := L)} : Set (ModGL Tag.E6 L)) := by simp
  rw [hEq]
  change frameA ^ i * frameT ^ j * frameX ^ k ∈
    Subgroup.closure ({frameA (L := L), frameT (L := L), frameX (L := L)} :
      Set (ModGL Tag.E6 L))
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.zpow_mem _ (Subgroup.subset_closure hA) i)
    (Subgroup.zpow_mem _ (Subgroup.subset_closure hT) j))
    (Subgroup.zpow_mem _ (Subgroup.subset_closure hX) k)

theorem weylTuple_cE6_torusTuple (e : Fin Tag.E6.rank → ℤ) :
    weylTuple cE6 (frameTorusTuple (L := L) e) =
      fun i => (frameOmega (L := L)) ^ (∑ j, frameCInvSingle i j * e j) := by
  funext i
  rw [weylTuple_cE6_apply, rootChar]
  simp only [frameTorusTuple, ← zpow_mul]
  rw [Finset.prod_zpow_eq_zpow_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weylTuple_cE6_torusTuple_expA :
    weylTuple cE6 (frameTorusTuple (L := L) frameExpA) =
      frameTorusTuple (L := L) frameExpA := by
  rw [weylTuple_cE6_torusTuple]
  funext i
  fin_cases i
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 0 j * frameExpA j) =
      frameTorusTuple (L := L) frameExpA 0
    rw [show (∑ j, frameCInvSingle 0 j * frameExpA j) =
      frameExpA 0 + 3 * (-3) by decide +kernel]
    rw [frameOmega_zpow_eq_of_eq_add_three_mul
      (a := frameExpA 0 + 3 * (-3)) (b := frameExpA 0) (m := -3) (by ring)]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 1 j * frameExpA j) =
      frameTorusTuple (L := L) frameExpA 1
    rw [show (∑ j, frameCInvSingle 1 j * frameExpA j) = frameExpA 1 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 2 j * frameExpA j) =
      frameTorusTuple (L := L) frameExpA 2
    rw [show (∑ j, frameCInvSingle 2 j * frameExpA j) = frameExpA 2 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 3 j * frameExpA j) =
      frameTorusTuple (L := L) frameExpA 3
    rw [show (∑ j, frameCInvSingle 3 j * frameExpA j) = frameExpA 3 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 4 j * frameExpA j) =
      frameTorusTuple (L := L) frameExpA 4
    rw [show (∑ j, frameCInvSingle 4 j * frameExpA j) = frameExpA 4 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 5 j * frameExpA j) =
      frameTorusTuple (L := L) frameExpA 5
    rw [show (∑ j, frameCInvSingle 5 j * frameExpA j) = frameExpA 5 by decide +kernel]
    rfl

theorem weylTuple_cE6_torusTuple_expT :
    weylTuple cE6 (frameTorusTuple (L := L) frameExpT) =
      frameTorusTuple (L := L) frameExpT := by
  rw [weylTuple_cE6_torusTuple]
  funext i
  fin_cases i
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 0 j * frameExpT j) =
      frameTorusTuple (L := L) frameExpT 0
    rw [show (∑ j, frameCInvSingle 0 j * frameExpT j) =
      frameExpT 0 + 3 * (-6) by decide +kernel]
    rw [frameOmega_zpow_eq_of_eq_add_three_mul
      (a := frameExpT 0 + 3 * (-6)) (b := frameExpT 0) (m := -6) (by ring)]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 1 j * frameExpT j) =
      frameTorusTuple (L := L) frameExpT 1
    rw [show (∑ j, frameCInvSingle 1 j * frameExpT j) = frameExpT 1 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 2 j * frameExpT j) =
      frameTorusTuple (L := L) frameExpT 2
    rw [show (∑ j, frameCInvSingle 2 j * frameExpT j) = frameExpT 2 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 3 j * frameExpT j) =
      frameTorusTuple (L := L) frameExpT 3
    rw [show (∑ j, frameCInvSingle 3 j * frameExpT j) = frameExpT 3 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 4 j * frameExpT j) =
      frameTorusTuple (L := L) frameExpT 4
    rw [show (∑ j, frameCInvSingle 4 j * frameExpT j) = frameExpT 4 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 5 j * frameExpT j) =
      frameTorusTuple (L := L) frameExpT 5
    rw [show (∑ j, frameCInvSingle 5 j * frameExpT j) = frameExpT 5 by decide +kernel]
    rfl

theorem weylTuple_cE6_torusTuple_expX :
    weylTuple cE6 (frameTorusTuple (L := L) frameExpX) =
      frameTorusTuple (L := L) frameExpX := by
  rw [weylTuple_cE6_torusTuple]
  funext i
  fin_cases i
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 0 j * frameExpX j) =
      frameTorusTuple (L := L) frameExpX 0
    rw [show (∑ j, frameCInvSingle 0 j * frameExpX j) =
      frameExpX 0 + 3 * (-2) by decide +kernel]
    rw [frameOmega_zpow_eq_of_eq_add_three_mul
      (a := frameExpX 0 + 3 * (-2)) (b := frameExpX 0) (m := -2) (by ring)]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 1 j * frameExpX j) =
      frameTorusTuple (L := L) frameExpX 1
    rw [show (∑ j, frameCInvSingle 1 j * frameExpX j) = frameExpX 1 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 2 j * frameExpX j) =
      frameTorusTuple (L := L) frameExpX 2
    rw [show (∑ j, frameCInvSingle 2 j * frameExpX j) = frameExpX 2 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 3 j * frameExpX j) =
      frameTorusTuple (L := L) frameExpX 3
    rw [show (∑ j, frameCInvSingle 3 j * frameExpX j) = frameExpX 3 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 4 j * frameExpX j) =
      frameTorusTuple (L := L) frameExpX 4
    rw [show (∑ j, frameCInvSingle 4 j * frameExpX j) = frameExpX 4 by decide +kernel]
    rfl
  · change (frameOmega (L := L)) ^ (∑ j, frameCInvSingle 5 j * frameExpX j) =
      frameTorusTuple (L := L) frameExpX 5
    rw [show (∑ j, frameCInvSingle 5 j * frameExpX j) = frameExpX 5 by decide +kernel]
    rfl

theorem frameTorusTuple_pow_three (e : Fin Tag.E6.rank → ℤ) :
    (frameTorusTuple (L := L) e) ^ 3 = 1 := by
  funext i
  simp only [Pi.pow_apply, Pi.one_apply, frameTorusTuple]
  rw [← zpow_natCast, ← zpow_mul]
  have hbase : (frameOmega (L := L)) ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact frameOmega_pow_three (L := L)
  rw [show e i * ((3 : ℕ) : ℤ) = (3 : ℤ) * e i by norm_num; ring, zpow_mul, hbase, one_zpow]

theorem frameA_pow_three : frameA (L := L) ^ 3 = 1 := by
  rw [frameA_eq_rootDiagUnit]
  change (rootDiagUnitHom Tag.E6 L (frameTorusTuple frameExpA)) ^ 3 = 1
  rw [← map_pow, frameTorusTuple_pow_three, map_one]

theorem frameT_pow_three : frameT (L := L) ^ 3 = 1 := by
  rw [frameT_eq_rootDiagUnit]
  change (rootDiagUnitHom Tag.E6 L (frameTorusTuple frameExpT)) ^ 3 = 1
  rw [← map_pow, frameTorusTuple_pow_three, map_one]

theorem frameX_pow_three : frameX (L := L) ^ 3 = 1 := by
  rw [frameX_eq_rootDiagUnit]
  change (rootDiagUnitHom Tag.E6 L (frameTorusTuple frameExpX)) ^ 3 = 1
  rw [← map_pow, frameTorusTuple_pow_three, map_one]

theorem frameGenProd_eq_rootDiagUnit (i j k : ℤ) :
    frameA (L := L) ^ i * frameT ^ j * frameX ^ k = rootDiagUnit Tag.E6
      (fun l => (frameOmega (L := L)) ^
        (i * frameExpA l + j * frameExpT l + k * frameExpX l)) := by
  have hA_hom : frameA (L := L) =
      rootDiagUnitHom Tag.E6 L (frameTorusTuple frameExpA) := by
    rw [frameA_eq_rootDiagUnit]; rfl
  have hT_hom : frameT (L := L) =
      rootDiagUnitHom Tag.E6 L (frameTorusTuple frameExpT) := by
    rw [frameT_eq_rootDiagUnit]; rfl
  have hX_hom : frameX (L := L) =
      rootDiagUnitHom Tag.E6 L (frameTorusTuple frameExpX) := by
    rw [frameX_eq_rootDiagUnit]; rfl
  have hpowA : frameA ^ i = rootDiagUnit Tag.E6
      (fun l => (frameOmega (L := L)) ^ (i * frameExpA l)) := by
    rw [hA_hom, ← map_zpow (rootDiagUnitHom Tag.E6 L)]
    change (rootDiagUnitHom Tag.E6 L) (frameTorusTuple frameExpA ^ i) =
      (rootDiagUnitHom Tag.E6 L)
        (fun l => (frameOmega (L := L)) ^ (i * frameExpA l))
    congr 1
    funext l
    simp only [Pi.pow_apply, frameTorusTuple]
    rw [← zpow_mul, mul_comm]
  have hpowT : frameT ^ j = rootDiagUnit Tag.E6
      (fun l => (frameOmega (L := L)) ^ (j * frameExpT l)) := by
    rw [hT_hom, ← map_zpow (rootDiagUnitHom Tag.E6 L)]
    change (rootDiagUnitHom Tag.E6 L) (frameTorusTuple frameExpT ^ j) =
      (rootDiagUnitHom Tag.E6 L)
        (fun l => (frameOmega (L := L)) ^ (j * frameExpT l))
    congr 1
    funext l
    simp only [Pi.pow_apply, frameTorusTuple]
    rw [← zpow_mul, mul_comm]
  have hpowX : frameX ^ k = rootDiagUnit Tag.E6
      (fun l => (frameOmega (L := L)) ^ (k * frameExpX l)) := by
    rw [hX_hom, ← map_zpow (rootDiagUnitHom Tag.E6 L)]
    change (rootDiagUnitHom Tag.E6 L) (frameTorusTuple frameExpX ^ k) =
      (rootDiagUnitHom Tag.E6 L)
        (fun l => (frameOmega (L := L)) ^ (k * frameExpX l))
    congr 1
    funext l
    simp only [Pi.pow_apply, frameTorusTuple]
    rw [← zpow_mul, mul_comm]
  rw [hpowA, hpowT, hpowX, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext l
  simp only [Pi.mul_apply]
  rw [← zpow_add, ← zpow_add]

theorem frameA_ne_one : frameA (L := L) ≠ 1 := by
  intro h
  have htuple : frameTorusTuple (L := L) frameExpA = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [frameA_eq_rootDiagUnit] at h
    simpa [rootDiagUnit_one] using h
  have h0 := congrFun htuple 0
  simp [frameTorusTuple, frameExpA] at h0
  exact frameOmega_ne_one h0

theorem frameT_not_mem_zpowers_frameA :
    frameT (L := L) ∉ Subgroup.zpowers (frameA (L := L)) := by
  intro h
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h
  have hprod : rootDiagUnit Tag.E6
      (fun l => (frameOmega (L := L)) ^ (i * frameExpA l + 0 * frameExpT l + 0 * frameExpX l)) =
      rootDiagUnit Tag.E6
      (fun l => (frameOmega (L := L)) ^ (0 * frameExpA l + 1 * frameExpT l + 0 * frameExpX l)) := by
    rw [← frameGenProd_eq_rootDiagUnit (L := L) i 0 0,
      ← frameGenProd_eq_rootDiagUnit (L := L) 0 1 0]
    simpa using hi
  have htup := CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := L) hprod
  have h0 : (frameOmega (L := L)) ^ i = (frameOmega (L := L)) ^ (2 : ℤ) := by
    have := congrFun htup 0
    simpa [frameExpA, frameExpT] using this
  have h1 : (frameOmega (L := L)) ^ i = (frameOmega (L := L)) ^ (1 : ℤ) := by
    have := congrFun htup 1
    simpa [frameExpA, frameExpT] using this
  have h21 : (frameOmega (L := L)) ^ (2 : ℤ) = (frameOmega (L := L)) ^ (1 : ℤ) :=
    h0.symm.trans h1
  have hone : (frameOmega (L := L)) = 1 := by
    have := congrArg (fun z => z * (frameOmega (L := L))⁻¹) h21
    rw [zpow_two, zpow_one] at this
    have hleft : (frameOmega (L := L)) * (frameOmega (L := L)) * (frameOmega (L := L))⁻¹ =
        (frameOmega (L := L)) := by group
    rw [hleft] at this
    simpa using this
  exact frameOmega_ne_one hone

theorem frameA_mul_frameT : frameA (L := L) * frameT = frameT * frameA := by
  rw [frameA_eq_rootDiagUnit, frameT_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext i
  simp [Pi.mul_apply, mul_comm]

theorem frameA_mul_frameX : frameA (L := L) * frameX = frameX * frameA := by
  rw [frameA_eq_rootDiagUnit, frameX_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext i
  simp [Pi.mul_apply, mul_comm]

theorem frameT_mul_frameX : frameT (L := L) * frameX = frameX * frameT := by
  rw [frameT_eq_rootDiagUnit, frameX_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  congr 1
  funext i
  simp [Pi.mul_apply, mul_comm]

theorem frameA_normalizes_zpowers_frameT :
    Subgroup.zpowers (frameA (L := L)) ≤
      Subgroup.normalizer (Subgroup.zpowers (frameT (L := L)) : Set (ModGL Tag.E6 L)) := by
  have hcomm : Commute (frameA (L := L)) (frameT (L := L)) := frameA_mul_frameT
  refine Subgroup.zpowers_le.mpr ?_
  refine (Subgroup.mem_normalizer_iff).mpr ?_
  intro t'
  constructor
  · intro ht'
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht'
    have hconj1 : frameA (L := L) * frameT (L := L) ^ j * (frameA (L := L))⁻¹ =
        frameT (L := L) ^ j := by
      calc frameA (L := L) * frameT (L := L) ^ j * (frameA (L := L))⁻¹ =
            frameT (L := L) ^ j * frameA (L := L) * (frameA (L := L))⁻¹ := by
            rw [(hcomm.zpow_right j).eq]
        _ = frameT (L := L) ^ j := by group
    rw [hconj1]
    exact Subgroup.zpow_mem (Subgroup.zpowers (frameT (L := L)))
      (Subgroup.mem_zpowers (frameT (L := L))) j
  · intro ht'
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ht'
    have hconj : (frameA (L := L))⁻¹ * frameT (L := L) ^ j * frameA (L := L) =
        frameT (L := L) ^ j := by
      calc (frameA (L := L))⁻¹ * frameT (L := L) ^ j * frameA (L := L) =
            frameT (L := L) ^ j * (frameA (L := L))⁻¹ * frameA (L := L) := by
            rw [(hcomm.inv_left.zpow_right j).eq]
        _ = frameT (L := L) ^ j := by group
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨j, ?_⟩
    calc frameT (L := L) ^ j = (frameA (L := L))⁻¹ * frameT (L := L) ^ j * frameA (L := L) := hconj.symm
      _ = (frameA (L := L))⁻¹ * (frameA (L := L) * t' * (frameA (L := L))⁻¹) * frameA (L := L) := by rw [hj]
      _ = t' := by group

theorem frameX_not_mem_sup_frameA_frameT :
    frameX (L := L) ∉ Subgroup.zpowers (frameA (L := L)) ⊔
      Subgroup.zpowers (frameT (L := L)) := by
  intro h
  have hset : frameX (L := L) ∈
      ((Subgroup.zpowers (frameA (L := L)) ⊔
        Subgroup.zpowers (frameT (L := L)) : Subgroup (ModGL Tag.E6 L)) : Set (ModGL Tag.E6 L)) := h
  rw [Subgroup.coe_mul_of_left_le_normalizer_right
      (Subgroup.zpowers (frameA (L := L)))
      (Subgroup.zpowers (frameT (L := L))) frameA_normalizes_zpowers_frameT] at hset
  rw [Set.mem_mul] at hset
  obtain ⟨a, ha, t, ht, hat⟩ := hset
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hprod : rootDiagUnit Tag.E6
      (fun l => (frameOmega (L := L)) ^ (i * frameExpA l + j * frameExpT l + 0 * frameExpX l)) =
      rootDiagUnit Tag.E6
      (fun l => (frameOmega (L := L)) ^ (0 * frameExpA l + 0 * frameExpT l + 1 * frameExpX l)) := by
    rw [← frameGenProd_eq_rootDiagUnit (L := L) i j 0,
      ← frameGenProd_eq_rootDiagUnit (L := L) 0 0 1]
    rw [zpow_zero, mul_one, zpow_zero, zpow_zero, one_mul, one_mul, zpow_one]
    exact hat
  have htup := CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := L) hprod
  have h3 : (frameOmega (L := L)) ^ (j * 2) = 1 := by
    have := congrFun htup 3
    simpa [frameExpA, frameExpT, frameExpX] using this
  have hj2 : ((frameOmega (L := L)) ^ j) ^ 2 = 1 := by
    rw [← zpow_natCast ((frameOmega (L := L)) ^ j) 2, ← zpow_mul]
    simpa using h3
  have hj3 : ((frameOmega (L := L)) ^ j) ^ 3 = 1 := by
    rw [← zpow_natCast ((frameOmega (L := L)) ^ j) 3, ← zpow_mul,
      show j * ((3 : ℕ) : ℤ) = (3 : ℤ) * j by norm_num; ring, zpow_mul]
    have hbase : (frameOmega (L := L)) ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact frameOmega_pow_three (L := L)
    rw [hbase, one_zpow]
  have hj1 : (frameOmega (L := L)) ^ j = 1 := by
    calc (frameOmega (L := L)) ^ j
        = ((frameOmega (L := L)) ^ j) ^ 3 * (((frameOmega (L := L)) ^ j) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hj3, hj2]; simp
  have hi1 : (frameOmega (L := L)) ^ (i + j) = 1 := by
    have h0 := congrFun htup 0
    simp [frameExpA, frameExpT, frameExpX] at h0
    rw [show i + j * 2 = (i + j) + j by ring, zpow_add] at h0
    rw [hj1, mul_one] at h0
    exact h0
  have h1 := congrFun htup 1
  simp [frameExpA, frameExpT, frameExpX] at h1
  rw [hi1] at h1
  exact frameOmega_ne_one (by simpa using h1.symm)

theorem frameD_eq_sup_zpowers :
    frameD (L := L) = Subgroup.zpowers (frameA (L := L)) ⊔
      Subgroup.zpowers (frameT (L := L)) ⊔ Subgroup.zpowers (frameX (L := L)) := by
  rw [frameD]
  rw [show ({frameA (L := L), frameT (L := L), frameX (L := L)} : Set (ModGL Tag.E6 L)) =
      {frameA (L := L)} ∪ {frameT (L := L)} ∪ {frameX (L := L)} by
    ext x; simp; tauto]
  rw [Subgroup.closure_union, Subgroup.closure_union,
    Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]

theorem frameD_card : Nat.card (frameD (L := L)) = 27 := by
  have h := CFSG.HardMathSupport.Solomon.LocalBalance.exists_isElemAbelian_card_three_of_independent
    (G := ModGL Tag.E6 L)
    (x := frameA (L := L)) (y := frameT (L := L)) (z := frameX (L := L))
    frameA_mul_frameT frameA_mul_frameX frameT_mul_frameX
    frameA_pow_three frameT_pow_three frameX_pow_three
    frameA_ne_one frameT_not_mem_zpowers_frameA frameX_not_mem_sup_frameA_frameT
  rw [frameD_eq_sup_zpowers]
  simpa using h.2

theorem weylTuple_mul (w : WeylGroup Tag.E6) (a b : Fin Tag.E6.rank → Lˣ) :
    weylTuple w (a * b) = weylTuple w a * weylTuple w b := by
  funext i
  simp only [weylTuple, Pi.mul_apply, rootChar, mul_zpow, Finset.prod_mul_distrib]

theorem weylTuple_inv (w : WeylGroup Tag.E6) (a : Fin Tag.E6.rank → Lˣ) :
    weylTuple w a⁻¹ = (weylTuple w a)⁻¹ := by
  funext i
  simp only [weylTuple, Pi.inv_apply, rootChar, inv_zpow, Finset.prod_inv_distrib]

theorem frameTorusTuple_pow_three_apply (e : Fin Tag.E6.rank → ℤ) :
    ∀ i, (frameTorusTuple (L := L) e) i ^ 3 = 1 := by
  intro i
  have h := congrFun (frameTorusTuple_pow_three (L := L) e) i
  simpa [Pi.pow_apply] using h

def frameCToralTuples : Set (Fin Tag.E6.rank → Lˣ) :=
  {b | (∀ i, b i ^ 3 = 1) ∧ weylTuple cE6 b = b}

def frameCToralSet : Set (ModGL Tag.E6 L) :=
  rootDiagUnit Tag.E6 '' frameCToralTuples

theorem frameA_mem_frameCToralSet : frameA (L := L) ∈ frameCToralSet (L := L) :=
  ⟨frameTorusTuple frameExpA, ⟨frameTorusTuple_pow_three_apply frameExpA, weylTuple_cE6_torusTuple_expA⟩,
    frameA_eq_rootDiagUnit.symm⟩

theorem frameT_mem_frameCToralSet : frameT (L := L) ∈ frameCToralSet (L := L) :=
  ⟨frameTorusTuple frameExpT, ⟨frameTorusTuple_pow_three_apply frameExpT, weylTuple_cE6_torusTuple_expT⟩,
    frameT_eq_rootDiagUnit.symm⟩

theorem frameX_mem_frameCToralSet : frameX (L := L) ∈ frameCToralSet (L := L) :=
  ⟨frameTorusTuple frameExpX, ⟨frameTorusTuple_pow_three_apply frameExpX, weylTuple_cE6_torusTuple_expX⟩,
    frameX_eq_rootDiagUnit.symm⟩

@[expose] noncomputable def frameCToralSubgroup : Subgroup (ModGL Tag.E6 L) where
  carrier := frameCToralSet (L := L)
  one_mem' := by
    refine ⟨1, ⟨?_, ?_⟩, rootDiagUnit_one⟩
    · intro i; simp
    · funext i
      simp [weylTuple, rootChar]
  mul_mem' := by
    rintro _ _ ⟨a, ⟨ha3, hafix⟩, rfl⟩ ⟨b, ⟨hb3, hbfix⟩, rfl⟩
    refine ⟨a * b, ⟨?_, ?_⟩, rootDiagUnit_mul a b⟩
    · intro i
      rw [Pi.mul_apply, mul_pow, ha3 i, hb3 i, one_mul]
    · rw [weylTuple_mul, hafix, hbfix]
  inv_mem' := by
    rintro _ ⟨a, ⟨ha3, hafix⟩, rfl⟩
    refine ⟨a⁻¹, ⟨?_, ?_⟩, rootDiagUnit_inv a⟩
    · intro i
      rw [Pi.inv_apply, inv_pow, ha3 i, inv_one]
    · rw [weylTuple_inv, hafix]

theorem frameD_le_frameCToralSubgroup : frameD (L := L) ≤ frameCToralSubgroup (L := L) := by
  rw [frameD]
  refine (Subgroup.closure_le (frameCToralSubgroup (L := L))).2 ?_
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact frameA_mem_frameCToralSet
  · exact frameT_mem_frameCToralSet
  · exact frameX_mem_frameCToralSet

theorem frameCToralSubgroup_le_frameD : frameCToralSubgroup (L := L) ≤ frameD (L := L) := by
  rintro t ⟨b, ⟨hb, hfix⟩, rfl⟩
  obtain ⟨h05, h12, h24⟩ := weylTuple_cE6_eq_imp b hfix
  exact frameCToralTuple_mem_frameD b hb h05 h12 h24

theorem frameCToralSubgroup_eq_frameD : frameCToralSubgroup (L := L) = frameD (L := L) :=
  le_antisymm frameCToralSubgroup_le_frameD frameD_le_frameCToralSubgroup

theorem frame_actualE_torus_eq_frameD
    {E : Subgroup (ModGL Tag.E6 L)} [Finite E]
    (hEM : E ≤ monomialSubgroup Tag.E6 L)
    (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4)
    (hWeyl : ∀ e (he : e ∈ E),
      weylQuotientHom Tag.E6 L ⟨e, hEM he⟩ ∈ Subgroup.zpowers cE6)
    {x : ModGL Tag.E6 L} (hxE : x ∈ E)
    (hxc : weylQuotientHom Tag.E6 L ⟨x, hEM hxE⟩ = cE6) :
    E ⊓ torusGroup Tag.E6 L = frameD (L := L) := by
  classical
  let D : Subgroup (ModGL Tag.E6 L) := E ⊓ torusGroup Tag.E6 L
  let φ : E →* WeylGroup Tag.E6 :=
    (weylQuotientHom Tag.E6 L).comp (Subgroup.inclusion hEM)
  have hφx : φ ⟨x, hxE⟩ = cE6 := hxc
  have hrange_le : φ.range ≤ Subgroup.zpowers cE6 := by
    rintro w ⟨e, rfl⟩
    exact hWeyl e e.2
  have hrange_ge : Subgroup.zpowers cE6 ≤ φ.range := by
    refine Subgroup.zpowers_le.mpr ?_
    exact ⟨⟨x, hxE⟩, hφx⟩
  have hrange : φ.range = Subgroup.zpowers cE6 := le_antisymm hrange_le hrange_ge
  have hc3 : orderOf cE6 = 3 := orderOf_eq_prime cE6_pow_three cE6_ne_one
  have hrange_card : Nat.card φ.range = 3 := by
    rw [hrange, Nat.card_zpowers, hc3]
  have hcard_ker : Nat.card φ.ker = 27 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hcard, hrange_card] at h
    omega
  have hker_eq : φ.ker = D.subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro he
      refine ⟨e.2, ?_⟩
      exact CFSG.HardMathSupport.Timmesfeld.CrossChar.mem_torusGroup_of_weylQuotientHom_eq_one
        (hEM e.2) he
    · rintro ⟨-, heT⟩
      have hmaps : MapsRootLines (e : ModGL Tag.E6 L) 1 := by
        simpa using mapsRootLines_of_mem_torusGroup heT
      exact weylQuotientHom_eq (w := 1) hmaps
  have hDcard : Nat.card D = 27 := by
    rw [← Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show D ≤ E from inf_le_left)).toEquiv]
    rw [← hker_eq, hcard_ker]
  have hle : D ≤ frameD (L := L) := by
    rintro d ⟨hdE, hdT⟩
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hdT
    have hd3 : (rootDiagUnit Tag.E6 b) ^ 3 = 1 := hE.2 (rootDiagUnit Tag.E6 b) hdE
    have hb3 : ∀ i, b i ^ 3 = 1 := by
      intro i
      have hb : b ^ 3 = 1 := by
        apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := L)
        rw [← rootDiagUnit_pow, rootDiagUnit_one]
        exact hd3
      exact congrFun hb i
    have hcomm : x * rootDiagUnit Tag.E6 b * x⁻¹ = rootDiagUnit Tag.E6 b := by
      have hxd : x * rootDiagUnit Tag.E6 b = rootDiagUnit Tag.E6 b * x :=
        CFSG.StandardType.TableB.IsElemAbelian.comm hE hxE hdE
      rw [hxd, mul_assoc, mul_inv_cancel, mul_one]
    have hmaps : MapsRootLines x cE6 := by
      have h := mapsRootLines_weylQuotientHom
        (⟨x, hEM hxE⟩ : monomialSubgroup Tag.E6 L)
      rwa [hxc] at h
    have hconj := monomial_conj_rootDiagUnit_weylTuple
      (hx := hEM hxE) (w := cE6) hmaps b
    have hfix : weylTuple cE6 b = b :=
      CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E6) (K := L)
        (by rw [← hconj, hcomm])
    obtain ⟨h05, h12, h24⟩ := weylTuple_cE6_eq_imp b hfix
    exact frameCToralTuple_mem_frameD b hb3 h05 h12 h24
  haveI : Finite (frameD (L := L)) :=
    (Nat.card_pos_iff.mp (by rw [frameD_card]; norm_num)).2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [frameD_card, hDcard])

end Torsion

end CFSG.StandardType.TwE6E4bFrame
