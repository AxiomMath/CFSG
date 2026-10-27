module

public import CFSG.Sporadic.Co2Schreier.SixAction
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCyclicKernel
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.GroupTheory.ExtraspecialCentralizerInnerAut
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public import Certificates.Certificate2058
public import Certificates.Certificate2049
public import Certificates.Certificate2051
public import Certificates.Certificate2057
public import Certificates.Certificate2060
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenSymplectic
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Co2Schreier.Cores
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Mathieu
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry (isometryMatrixEquiv
  exists_symplectic_basis isometry_iff_matrix basisMatrixEquiv basisMatrixEquiv_mulVec)
open scoped Matrix

theorem sixChain_shapeOK :
    chainShapeOK witRec.wLocal.sixActionChain 63 2 12 [0, 1, 3, 7, 15, 31] = true :=
  Certificates.certificate2058

theorem sixChain_shape : ChainShape witRec.wLocal.sixActionChain 63 2 12 [0, 1, 3, 7, 15, 31] :=
  chainShape_of sixChain_shapeOK

@[expose] def sixChain : RawSchreierDatum 63 :=
  rawOfArrays 63 witRec.wLocal.sixActionChain.origArrs witRec.wLocal.sixActionChain.strongArrs
    witRec.wLocal.sixActionChain.baseArr witRec.wLocal.sixActionChain.wordArrs (by norm_num)
    (by rw [sixChain_shape.origArrs_size, sixChain_shape.strongArrs_size]; norm_num)
    (baseArr_lt_of_shape sixChain_shape (by decide))
    (baseArr_nodup_of_shape sixChain_shape (by decide))

theorem sixChain_records : witRec.wLocal.sixActionChain.Records sixChain :=
  records_rawOfArrays_of_shape sixChain_shape _ _ _ _ (by norm_num)

theorem card_sixChain : Nat.card sixChain.originalSubgroup = 1451520 := by
  rw [card_originalSubgroup_of_chainOK sixChain_records.2.2 (by norm_num) sixFacts.chain]
  change (recordOrbits 63 witRec.wLocal.sixActionChain).prod = _
  rw [sixFacts.orbits]
  rfl

@[expose] def sixPi (i : ℕ) : Equiv.Perm (Fin 63) :=
  permOfArr 63 witRec.wLocal.sixActionChain.origArrs[i]!

theorem rep_sixPi {i : ℕ} (hi : i < 2) :
    Rep 63 witRec.wLocal.sixActionChain.origArrs[i]! (sixPi i) :=
  (rep_permOfArr (sixChain_shape.orig_inv hi)).1

theorem sixChain_original :
    sixChain.originalSubgroup = Subgroup.closure {π | ∃ i < 2, sixPi i = π} := by
  rw [RawSchreierDatum.originalSubgroup]
  congr 1
  ext π
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  unfold sixChain
  rw [original_toList_rawOfArrays, sixChain_shape.origArrs_size]
  rfl

@[expose] def sixPt (p : ℕ) : V6 := sixBasis.equivFun.symm (toVecD 6 (p + 1))

theorem sixPt_ne_zero {p : ℕ} (hp : p < 63) : sixPt p ≠ 0 := by
  intro h
  have h1 := congrArg sixBasis.equivFun h
  rw [sixPt, LinearEquiv.apply_symm_apply, map_zero, ← toVecD_zero 6] at h1
  have := toVecD_injective (by omega) (by norm_num) h1
  omega

theorem sixPt_injective {p q : ℕ} (hp : p < 63) (hq : q < 63) (h : sixPt p = sixPt q) :
    p = q := by
  have h1 := congrArg sixBasis.equivFun h
  rw [sixPt, sixPt, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
  have := toVecD_injective (by omega) (by omega) h1
  omega

theorem card_V6 : Nat.card V6 = 64 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_V6, Nat.card_zmod]
  rfl

theorem card_nonzero_V6 : Nat.card {v : V6 // v ≠ 0} = 63 := by
  have : Fintype V6 := Fintype.ofFinite V6
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    ← Nat.card_eq_fintype_card, card_V6]

@[expose] def nzEquiv : Fin 63 ≃ {v : V6 // v ≠ 0} :=
  Equiv.ofBijective (fun p => ⟨sixPt p, sixPt_ne_zero p.2⟩)
    ((Nat.bijective_iff_injective_and_card _).2
      ⟨fun a b h => Fin.ext (sixPt_injective a.2 b.2 (congrArg Subtype.val h)),
        by rw [card_nonzero_V6, Nat.card_eq_fintype_card, Fintype.card_fin]⟩)

@[expose] def nzPerm : (V6 ≃ₗ[ZMod 2] V6) →* Equiv.Perm {v : V6 // v ≠ 0} where
  toFun g := g.toEquiv.subtypeEquiv fun v => by
    simp only [ne_eq, LinearEquiv.coe_toEquiv, LinearEquiv.map_eq_zero_iff]
  map_one' := Equiv.ext fun _ => rfl
  map_mul' _ _ := Equiv.ext fun _ => rfl

@[expose] def toPerm63 : (V6 ≃ₗ[ZMod 2] V6) →* Equiv.Perm (Fin 63) :=
  nzEquiv.symm.permCongrHom.toMonoidHom.comp nzPerm

theorem toPerm63_apply (g : V6 ≃ₗ[ZMod 2] V6) (p : Fin 63) :
    nzEquiv (toPerm63 g p) = ⟨g (nzEquiv p), (nzPerm g (nzEquiv p)).2⟩ := by
  change nzEquiv (nzEquiv.symm (nzPerm g (nzEquiv.symm.symm p))) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem toPerm63_injective : Function.Injective toPerm63 := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine LinearEquiv.ext fun v => ?_
  by_cases hv : v = 0
  · rw [hv, map_zero]
    rfl
  · obtain ⟨p, hp⟩ := nzEquiv.surjective ⟨v, hv⟩
    have := toPerm63_apply g p
    rw [hg, Equiv.Perm.one_apply, hp] at this
    exact (congrArg Subtype.val this).symm

theorem colsOf_get (rows : List ℕ) {k : ℕ} (hk : k < 6) : (colsOf rows)[k]! = colBits rows k := by
  rw [colsOf, getElem!_pos _ k (by simpa using hk)]
  simp

theorem toVecD_colMul (rows : List ℕ) (x : ℕ) :
    toVecD 6 (colMul rows x) = (Matrix.of fun j k : Fin 6 =>
      if (rows.getD j 0).testBit k then (1 : ZMod 2) else 0) *ᵥ toVecD 6 x := by
  rw [colMul, xorBits, foldl_xor_toVecD, toVecD_zero, zero_add]
  funext j
  rw [Matrix.mulVec, dotProduct, Finset.sum_apply]
  have hs : (colsOf rows).size = 6 := by simp [colsOf]
  rw [hs, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.of_apply, toVecD_apply 6 x k]
  by_cases hx : x.testBit k
  · rw [ite_eq_left hx, ite_eq_left hx, mul_one, colsOf_get rows k.2, toVecD_apply,
      colBits_testBit]
    simp [j.2]
  · rw [ite_eq_right hx, ite_eq_right hx, mul_zero, Pi.zero_apply]

theorem sixN_mulVec_toVecD {i : ℕ} (x : ℕ) :
    sixN i *ᵥ toVecD 6 x = toVecD 6 (colMul (witRec.wLocal.sixRows.getD i []) x) := by
  rw [toVecD_colMul]
  rfl

theorem sixAction_cGen_sixPt {i : ℕ} (hi : i < 2) {p : ℕ} (hp : p < 63) :
    sixAction (cGen i) (sixPt p) =
      sixPt ((witRec.wLocal.sixActionChain.origArrs[i]!)[p]!) := by
  apply sixBasis.equivFun.injective
  rw [← basisMatrixEquiv_mulVec sixBasis (sixAction (cGen i)) (sixPt p),
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_val,
    toMatrix_sixAction_cGen hi]
  simp only [sixPt, LinearEquiv.apply_symm_apply]
  rw [sixN_mulVec_toVecD, ← sixFacts.perm i hi p hp]

theorem toPerm63_sixAction_cGen {i : ℕ} (hi : i < 2) :
    toPerm63 (sixAction (cGen i)) = sixPi i := by
  refine Equiv.ext fun p => ?_
  apply nzEquiv.injective
  rw [toPerm63_apply]
  apply Subtype.ext
  change sixAction (cGen i) (sixPt p) = sixPt (sixPi i p)
  rw [sixAction_cGen_sixPt hi p.2, rep_sixPi hi p]

theorem top_locC :
    (⊤ : Subgroup locC) = Subgroup.closure {c : locC | (c : Equiv.Perm (Fin 2300)) ∈ cTuple} :=
  (Subgroup.closure_closure_coe_preimage (k := {g | g ∈ cTuple})).symm

theorem sixAction_range :
    sixAction.range = Subgroup.closure {g | ∃ i < 2, sixAction (cGen i) = g} := by
  rw [MonoidHom.range_eq_map, top_locC, MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨i, hi, hci⟩ := (mem_iff_exists_getD (d := 1)).1 (show (c : Equiv.Perm (Fin 2300)) ∈
      cTuple from hc)
    refine ⟨i, by rwa [cTuple_length] at hi, ?_⟩
    congr 1
    exact Subtype.ext hci
  · rintro ⟨i, hi, rfl⟩
    exact ⟨cGen i, getD_mem (by rw [cTuple_length]; exact hi), rfl⟩

theorem card_sixAction_range : Nat.card sixAction.range = 1451520 := by
  have himg : toPerm63 '' {g | ∃ i < 2, sixAction (cGen i) = g} = {π | ∃ i < 2, sixPi i = π} := by
    ext π
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      exact ⟨i, hi, (toPerm63_sixAction_cGen hi).symm⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨_, ⟨i, hi, rfl⟩, toPerm63_sixAction_cGen hi⟩
  rw [← Subgroup.card_map_of_injective toPerm63_injective, sixAction_range, MonoidHom.map_closure,
    himg, ← sixChain_original, card_sixChain]

@[expose] def sixNLit (i : ℕ) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun j k => if (([[59, 52, 53, 56, 22, 16], [4, 15, 28, 21, 16, 50]].getD i []).getD j
    0).testBit k then 1 else 0

theorem sixN_eq (i : ℕ) : sixN i = sixNLit i := by
  rw [sixN, sixNLit, six_rows_eq]

theorem sixNLit_isometry : ∀ i < 2, (sixNLit i)ᵀ * sixGramLit * sixNLit i = sixGramLit := by
  decide

theorem sixAction_cGen_mem {i : ℕ} (hi : i < 2) :
    sixAction (cGen i) ∈ TauCeti.BilinForm.isometryGroup sixForm := by
  refine (isometry_iff_matrix sixBasis sixForm _).2 ?_
  rw [CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv_val,
    toMatrix_sixAction_cGen hi, toMatrix_sixForm, sixN_eq, sixGram_eq]
  exact sixNLit_isometry i hi

theorem sixAction_range_le : sixAction.range ≤ TauCeti.BilinForm.isometryGroup sixForm := by
  rw [sixAction_range, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact sixAction_cGen_mem hi

theorem card_isometryGroup_sixForm :
    Nat.card (TauCeti.BilinForm.isometryGroup sixForm) = 1451520 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_isometryGroup 3 sixForm
    sixForm_isAlt sixForm_nondegenerate (by rw [finrank_V6]), Nat.card_zmod]
  decide

theorem sixAction_range_eq : sixAction.range = TauCeti.BilinForm.isometryGroup sixForm := by
  have : Finite (TauCeti.BilinForm.isometryGroup sixForm) :=
    Nat.finite_of_card_ne_zero (by rw [card_isometryGroup_sixForm]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge sixAction_range_le
    (le_of_eq (by rw [card_isometryGroup_sixForm, card_sixAction_range]))

theorem locQ_le_kerMap : locQ ≤ sixAction.ker.map locC.subtype := by
  rw [locQ, Subgroup.closure_le]
  intro g hg
  obtain ⟨m, hm, rfl⟩ := (mem_iff_exists_getD (d := 1)).1 hg
  rw [qTuple_length] at hm
  exact ⟨qGen m, sixAction_qGen hm, rfl⟩

theorem locQ_le_ker : locQ.subgroupOf locC ≤ sixAction.ker := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := locQ_le_kerMap (Subgroup.mem_subgroupOf.1 hx)
  rwa [Subtype.ext hyx] at hy

theorem card_locQ_subgroupOf : Nat.card (locQ.subgroupOf locC) = 512 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe locQ_le_C).toEquiv, card_locQ]

theorem sixAction_ker : sixAction.ker = locQ.subgroupOf locC := by
  have h := sixAction.ker.card_mul_index
  rw [Subgroup.index_ker, card_sixAction_range, card_locC] at h
  have hk : Nat.card sixAction.ker = 512 :=
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1451520) (h.trans (by norm_num))
  exact (Subgroup.eq_of_le_of_card_ge locQ_le_ker
    (le_of_eq (by rw [hk, card_locQ_subgroupOf]))).symm

theorem card_quotient_CQ : Nat.card (locC ⧸ locQ.subgroupOf locC) = 1451520 := by
  have h := (locQ.subgroupOf locC).card_eq_card_quotient_mul_card_subgroup
  rw [card_locC, card_locQ_subgroupOf] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 512) (h.symm.trans (by norm_num))

@[expose] def quotCQEquivIsometry :
    locC ⧸ locQ.subgroupOf locC ≃* TauCeti.BilinForm.isometryGroup sixForm :=
  (QuotientGroup.quotientMulEquivOfEq sixAction_ker.symm).trans
    ((QuotientGroup.quotientKerEquivRange sixAction).trans
      (MulEquiv.subgroupCongr sixAction_range_eq))

theorem nonempty_isometry_equiv_statedSp :
    Nonempty (TauCeti.BilinForm.isometryGroup sixForm ≃* StatedSp 3 (ZMod 2)) := by
  obtain ⟨m, b, hdim, hb⟩ := exists_symplectic_basis sixForm sixForm_isAlt sixForm_nondegenerate
  rw [finrank_V6] at hdim
  have hm : m = 3 := by omega
  subst hm
  exact ⟨(isometryMatrixEquiv b sixForm hb).trans
    (MulEquiv.subgroupCongr CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm)⟩

theorem nonempty_quotCQ_equiv_statedSp :
    Nonempty (locC ⧸ locQ.subgroupOf locC ≃* StatedSp 3 (ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_isometry_equiv_statedSp
  exact ⟨quotCQEquivIsometry.trans e⟩

theorem isSimpleGroup_statedSp_three_two : IsSimpleGroup (StatedSp 3 (ZMod 2)) := by
  have : IsSimpleGroup (StatedProj (StatedSp 3 (ZMod 2))) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) 3 (by norm_num)
      (Or.inr (Or.inr ⟨Nat.card_zmod 2, le_rfl⟩))
  exact CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.projEquiv.isSimpleGroup

theorem isSimpleGroup_quotCQ : IsSimpleGroup (locC ⧸ locQ.subgroupOf locC) := by
  obtain ⟨e⟩ := nonempty_quotCQ_equiv_statedSp
  have := isSimpleGroup_statedSp_three_two
  exact e.isSimpleGroup

theorem not_isMulCommutative_quotCQ : ¬ IsMulCommutative (locC ⧸ locQ.subgroupOf locC) := by
  intro h
  have : IsSimpleGroup (locC ⧸ locQ.subgroupOf locC) := isSimpleGroup_quotCQ
  let _ : CommGroup (locC ⧸ locQ.subgroupOf locC) :=
    { (inferInstance : Group (locC ⧸ locQ.subgroupOf locC)) with
      mul_comm := fun a b => h.is_comm.comm a b }
  have hp := IsSimpleGroup.prime_card (α := locC ⧸ locQ.subgroupOf locC)
  rw [card_quotient_CQ] at hp
  rcases hp.eq_one_or_self_of_dvd 2 (by norm_num) with h2 | h2 <;> norm_num at h2

theorem commutator_quotCQ : commutator (locC ⧸ locQ.subgroupOf locC) = ⊤ :=
  CFSG.GroupTheory.commutator_eq_top_of_isSimpleGroup isSimpleGroup_quotCQ
    not_isMulCommutative_quotCQ

theorem CTUC_Co2_first_centralizer_symplectic_quotient :
    LinearIndependent (ZMod 2) sixVec ∧ (∀ k, (sixBasis k : Co2V) = sixVec k) ∧
    Module.finrank (ZMod 2) V6 = 6 ∧
    (∀ c : locC, V6.map (linC c : Co2V →ₗ[ZMod 2] Co2V) = V6) ∧
    LinearMap.BilinForm.toMatrix sixBasis sixForm = sixGram ∧ sixGramᵀ = sixGram ∧
    (∀ k, sixGram k k = 0) ∧ sixGram.det ≠ 0 ∧ sixForm.IsAlt ∧ sixForm.Nondegenerate ∧
    sixAction.range = TauCeti.BilinForm.isometryGroup sixForm ∧
    sixAction.ker = locQ.subgroupOf locC ∧
    Nonempty (locC ⧸ locQ.subgroupOf locC ≃* StatedSp 3 (ZMod 2)) ∧
    Nonempty (locC ⧸ locQ.subgroupOf locC ≃* StatedProj (StatedSp 3 (ZMod 2))) ∧
    Nat.card (locC ⧸ locQ.subgroupOf locC) = 1451520 ∧
    IsSimpleGroup (locC ⧸ locQ.subgroupOf locC) ∧
    ¬ IsMulCommutative (locC ⧸ locQ.subgroupOf locC) ∧
    commutator (locC ⧸ locQ.subgroupOf locC) = ⊤ := by
  obtain ⟨e⟩ := nonempty_quotCQ_equiv_statedSp
  refine ⟨sixVec_linearIndependent, sixBasis_apply, finrank_V6, V6_map, toMatrix_sixForm, ?_, ?_,
    sixGram_eq ▸ sixGramLit_det_ne_zero, sixForm_isAlt, sixForm_nondegenerate, sixAction_range_eq,
    sixAction_ker, ⟨e⟩,
    ⟨e.trans CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.projEquiv⟩,
    card_quotient_CQ, isSimpleGroup_quotCQ, not_isMulCommutative_quotCQ, commutator_quotCQ⟩
  · rw [sixGram_eq]
    exact sixGramLit_symm
  · intro k
    rw [sixGram_eq]
    exact sixGramLit_diag k

end CFSG.Sporadic.Co2Schreier
