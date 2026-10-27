module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEsu
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSExcl
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGQTwoNativeGen
public import CFSG.LocalAnalysis.StandardType.GGNbrU63
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrG1
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxKb
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
import CFSG.LocalAnalysis.StandardType.GGTorusGenRkComp
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeSU
import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSU
import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutMain
import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType
open CFSG.Assembly
open CFSG.Blueprint
open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal.Unitary
open Matrix CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private noncomputable def qTwoNbrG2_conjNAut {d n : ℕ} {K : Type} [Field K]
    (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K))) :
    MulAut ↥(unitarySU 2 n K d) where
  toFun := LineU.conjN D hD
  invFun := LineU.conjN D⁻¹ (Subgroup.inv_mem _ hD)
  left_inv s := by
    apply Subtype.ext
    rw [LineU.coe_conjN, LineU.coe_conjN]
    group
  right_inv s := by
    apply Subtype.ext
    rw [LineU.coe_conjN, LineU.coe_conjN]
    group
  map_mul' s u := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, LineU.coe_conjN]
    group

private theorem qTwoNbrG2_conjNAut_mul_diag {d n : ℕ} {K : Type} [Field K]
    {D : GL (Fin d) K}
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {t : Fin d → K} (hDt : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (s : ↥(unitarySU 2 n K d)) :
    (((qTwoNbrG2_conjNAut D hD s : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) * diagonal t =
      diagonal t * ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  have h : (((qTwoNbrG2_conjNAut D hD s : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) * D =
      D * (s : GL (Fin d) K) := by
    show ((LineU.conjN D hD s : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * D =
      D * (s : GL (Fin d) K)
    rw [LineU.coe_conjN]
    group
  have hm := congrArg (fun x : GL (Fin d) K => ((x : Matrix (Fin d) (Fin d) K))) h
  simp only [Units.val_mul] at hm
  simpa only [← hDt] using hm

private theorem qTwoNbrG2_not_solvable {H : Type*} [Group H] (hH : CFSG.IsQuasisimple H) :
    ¬ Group.IsSolvable H := by
  obtain ⟨hperf, hsimple, -⟩ := hH
  haveI : Nontrivial (H ⧸ Subgroup.center H) := hsimple.toNontrivial
  haveI : Nontrivial H := (QuotientGroup.mk'_surjective (Subgroup.center H)).nontrivial
  haveI : Group.IsPerfect H := hperf
  exact Group.IsPerfect.not_isSolvable H

theorem qTwoNbr_fourBlock {p : ℕ} {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hM : QTwoNbrModel p B Bs x L D J y K) :
    ggQTwoNbrBlockProp hM := by
  letI := hM.groupQ
  letI := hM.fieldF0
  letI := hM.finiteF0
  letI := hM.charF0
  letI := hM.factF0
  have hcomp : IsComponentOf hM.Jbar
      (hM.Kbar ⊓ Subgroup.centralizer ({hM.xbar} : Set hM.Q)) :=
    (qTwoNbr_comp_transport hM).1
  have hcard : Nat.card hM.F0 = ((2 : ℕ) ^ 1) ^ 2 := by rw [hM.hcardF0]; norm_num
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 hM.F0 :=
    ⟨Nat.prime_two, le_refl 1, by rw [hM.hcardF0]; norm_num⟩
  let e : Su hM.F0 2 1 hM.d ≃* ↥(unitarySU 2 1 hM.F0 hM.d) :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.suEquivUnitarySU hM.F0 2 1 hcard hM.d
  have hKb : hM.ψ.range = hM.Kbar := hM.hψ_range
  let ψb : Su hM.F0 2 1 hM.d →* ↥hM.Kbar :=
    (MulEquiv.subgroupCongr hKb).toMonoidHom.comp hM.ψ.rangeRestrict
  let φ : ↥(unitarySU 2 1 hM.F0 hM.d) →* ↥hM.Kbar := ψb.comp e.symm.toMonoidHom
  have hφsurj : Function.Surjective φ :=
    ((MulEquiv.subgroupCongr hKb).surjective.comp
      (MonoidHom.rangeRestrict_surjective hM.ψ)).comp e.symm.surjective
  have hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 1 hM.F0 hM.d) := by
    intro s hs
    have hs1 : e.symm s ∈ hM.ψ.ker := by
      rw [MonoidHom.mem_ker]
      have h1 : ψb (e.symm s) = 1 := MonoidHom.mem_ker.mp hs
      exact congrArg Subtype.val h1
    have hcen : e.symm s ∈ Subgroup.center (Su hM.F0 2 1 hM.d) := hM.hψ_ker hs1
    rw [Subgroup.mem_center_iff]
    intro t
    exact e.symm.injective (by
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hcen (e.symm t))
  have hxbarAs : hM.xbar ∈ hM.As := by
    rw [hM.hxbar, hM.hAs]
    exact MonoidHom.mem_range.mpr ⟨⟨x, hM.hxBs⟩, rfl⟩
  have hAsN : hM.As ≤ Subgroup.normalizer (hM.Kbar : Set hM.Q) := by
    intro b hb
    rw [hM.hAs] at hb
    obtain ⟨b0, rfl⟩ := MonoidHom.mem_range.mp hb
    rw [hM.hKbar]
    exact qTwoNbrRec_mem_normalizer_Kb hM.q hM.hBsN b0.2
  let a : MulAut ↥hM.Kbar := ggGamma hM.Kbar hAsN ⟨hM.xbar, hxbarAs⟩
  obtain ⟨g, hgdiag, hunit⟩ := hM.hdiag hM.xbar hxbarAs
  obtain ⟨t, ht⟩ := hgdiag
  have hD : g ∈ Subgroup.normalizer (unitarySU 2 1 hM.F0 hM.d : Set (GL (Fin hM.d) hM.F0)) := by
    rw [show unitarySU 2 1 hM.F0 hM.d = _ from
      (SUid_eq_statedSU (p := 2) (f := 1) hcard hM.d).symm]
    exact CFSG.StandardType.InnerDiagSU.mem_normalizer_SUid hunit.1
  have htne : ∀ i, t i ≠ 0 := fun i => LineU.diag_ne_zero_of_eq ht i
  let δ : MulAut ↥(unitarySU 2 1 hM.F0 hM.d) := qTwoNbrG2_conjNAut g hD
  have hδ : ∀ s : ↥(unitarySU 2 1 hM.F0 hM.d),
      (((δ s : ↥(unitarySU 2 1 hM.F0 hM.d)) : GL (Fin hM.d) hM.F0) :
          Matrix (Fin hM.d) (Fin hM.d) hM.F0) * diagonal t =
        diagonal t * ((s : GL (Fin hM.d) hM.F0) : Matrix (Fin hM.d) (Fin hM.d) hM.F0) :=
    fun s => qTwoNbrG2_conjNAut_mul_diag hD ht s
  have hact : ∀ s : ↥(unitarySU 2 1 hM.F0 hM.d),
      a (φ s) = φ (LineU.conjN g hD s) := by
    intro s
    apply Subtype.ext
    rw [show ((a (φ s) : ↥hM.Kbar) : hM.Q) =
        hM.xbar * ((φ s : ↥hM.Kbar) : hM.Q) * hM.xbar⁻¹ from
      ggGamma_coe hM.Kbar hAsN ⟨hM.xbar, hxbarAs⟩ (φ s)]
    show hM.xbar * hM.ψ (e.symm s) * hM.xbar⁻¹ = hM.ψ (e.symm (LineU.conjN g hD s))
    obtain ⟨y, hyGL, hyact⟩ := hunit.2 (e.symm s)
    rw [hyact]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.coe_suEquivUnitarySU_symm,
      LineU.coe_conjN, hyGL,
      CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.coe_suEquivUnitarySU_symm]
  have hggFix_sub : hM.Kbar ⊓ Subgroup.centralizer ({hM.xbar} : Set hM.Q) =
      (ggFix a).map hM.Kbar.subtype :=
    (map_ggFix_ggGamma (L := hM.Kbar) (hBN := hAsN) ⟨hM.xbar, hxbarAs⟩).symm
  have hJ : IsComponentOf (hM.Jbar.subgroupOf hM.Kbar) (ggFix a) := by
    have h1 : IsComponentOf hM.Jbar ((ggFix a).map hM.Kbar.subtype) := by
      rw [← hggFix_sub]
      exact hcomp
    exact (isComponentOf_comap_of_injective hM.Kbar.subtype hM.Kbar.subtype_injective h1).1
  obtain ⟨Q, hQ, hQmap⟩ :=
    SCFourCover.exists_isComponentOf_map_eq (ψ := φ) hφsurj hker (a := δ) (φ := a)
      (fun s => hact s) hJ
  obtain ⟨i₀, hScard2, hQeq⟩ :=
    eq_blockSU_of_isComponentOf_ggFix_diag hUF htne δ hδ hQ
  classical
  let S : Finset (Fin hM.d) := Finset.univ.filter (fun i => t i = t i₀)
  have hQeqS : Q = TableBUE.blockSU (K := hM.F0) (n := 1) S := hQeq
  have hScard2S : 2 ≤ S.card := hScard2
  have hJ'eq : hM.Jbar.subgroupOf hM.Kbar =
      (TableBUE.blockSU (K := hM.F0) (n := 1) S).map φ := by
    rw [← hQeqS]
    exact hQmap.symm
  have hcard4 : 4 ≤ S.card := by
    by_contra hlt
    have hS3 : S.card ≤ 3 := by omega
    have hS1 : 1 ≤ S.card := le_trans (by norm_num) hScard2S
    have hsol : Group.IsSolvable ↥((TableBUE.blockSU (K := hM.F0) (n := 1) S).map φ) :=
      WitSU.isSolvable_map_blockSU_two_one hUF φ hS1 hS3
    have hJ'q : CFSG.IsQuasisimple ↥((TableBUE.blockSU (K := hM.F0) (n := 1) S).map φ) := by
      have h := (TableBSymp.isQuasisimple_iff ↥(hM.Jbar.subgroupOf hM.Kbar)).mp hJ.2.2
      rwa [hJ'eq] at h
    exact qTwoNbrG2_not_solvable hJ'q hsol
  obtain ⟨I, hIS, hIcard⟩ := Finset.exists_subset_card_eq hcard4
  have hJbar_le_Kbar : hM.Jbar ≤ hM.Kbar := by
    rw [hM.hJbar, hM.hKbar]
    rintro y ⟨j, rfl⟩
    exact ⟨Subgroup.inclusion hM.hJK j, rfl⟩
  have hJbar_eq : hM.Jbar = ((TableBUE.blockSU (K := hM.F0) (n := 1) S).map φ).map
      hM.Kbar.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hJbar_le_Kbar]
    exact congrArg (Subgroup.map hM.Kbar.subtype) hJ'eq
  have hψ_eq : hM.ψ = hM.Kbar.subtype.comp (φ.comp e.toMonoidHom) := by
    ext s
    change hM.ψ s = (ψb (e.symm (e s)) : hM.Q)
    rw [e.symm_apply_apply]
    rfl
  have hunitBlock : ∀ J : Finset (Fin hM.d),
      CFSG.SeitzReduction.UnitaryPilot.unitaryBlock hUF J =
        TableBUE.blockSU (K := hM.F0) (n := 1) J := by
    intro J
    ext z
    rw [CFSG.SeitzReduction.UnitaryPilot.mem_unitaryBlock, TableBUE.mem_blockSU]
    exact Iff.rfl
  have hmap_block : (coordBlockSU hM.F0 2 1 I).map e.toMonoidHom =
      TableBUE.blockSU (K := hM.F0) (n := 1) I := by
    change (coordBlockSU hM.F0 2 1 I).map
        (CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.suEquivUnitarySU hM.F0 2 1
          hcard hM.d).toMonoidHom =
      TableBUE.blockSU (K := hM.F0) (n := 1) I
    rw [← hunitBlock I]
    ext y
    rw [Subgroup.mem_map_equiv, mem_coordBlockSU_iff,
      CFSG.SeitzReduction.UnitaryPilot.mem_unitaryBlock]
    constructor
    · intro h i j hij
      have h' := h i j hij
      rw [Matrix.one_apply]
      rwa [CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.coe_suEquivUnitarySU_symm] at h'
    · intro h i j hij
      have h' := h i j hij
      rw [CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.coe_suEquivUnitarySU_symm]
      rwa [Matrix.one_apply] at h'
  have hblock_mono : TableBUE.blockSU (K := hM.F0) (n := 1) I ≤
      TableBUE.blockSU (K := hM.F0) (n := 1) S := by
    rw [← hunitBlock I, ← hunitBlock S]
    exact CFSG.SeitzReduction.UnitaryPilot.unitaryBlock_mono hUF hIS
  refine ⟨I, hIcard, ?_⟩
  rw [hJbar_eq]
  calc (coordBlockSU hM.F0 2 1 I).map hM.ψ
      = (((coordBlockSU hM.F0 2 1 I).map e.toMonoidHom).map φ).map hM.Kbar.subtype := by
        rw [hψ_eq, ← Subgroup.map_map, ← Subgroup.map_map]
    _ = ((TableBUE.blockSU (K := hM.F0) (n := 1) I).map φ).map hM.Kbar.subtype := by
        rw [hmap_block]
    _ ≤ ((TableBUE.blockSU (K := hM.F0) (n := 1) S).map φ).map hM.Kbar.subtype :=
        Subgroup.map_mono (f := hM.Kbar.subtype)
          (Subgroup.map_mono (f := φ) hblock_mono)

end CFSG.StandardType.QTwo

end
