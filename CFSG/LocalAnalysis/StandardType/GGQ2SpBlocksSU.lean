module

public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
public import CFSG.GroupTheory.WeirSylow.UnitaryBridge
public import CFSG.Assembly.Defs
public import CFSG.Assembly.LargeEvenDefs
import CFSG.Assembly.GL83StatedBridge
import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Open (StatedSU)
open CFSG.StandardType.ClassicalBlocks (GUFull)
open scoped commutatorElement

variable {G : Type} [Group G] {E : Type} [Field E] [Finite E] [CharP E 2]

private theorem mem_statedSU_of_mem_unitaryFull {m Q p f : ℕ} {E : Type} [Field E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E) (hQ : Q = p ^ f)
    {A : GL (Fin m) E} (hA : A ∈ GUFull m Q E)
    (hdet : (A : Matrix (Fin m) (Fin m) E).det = 1) : A ∈ StatedSU m Q E :=
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.mem_statedSU_of_mem_statedGU
    h hQ hA hdet

private theorem statedSU_eq_unitaryFull_inf_ker_det {m Q p f : ℕ} {E : Type} [Field E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E) (hQ : Q = p ^ f) :
    StatedSU m Q E = GUFull m Q E ⊓
      (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ).ker := by
  refine le_antisymm ?_ ?_
  · intro A hA
    refine ⟨?_, ?_⟩
    · exact CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU
        (q := Q) (n := m) (L := E) hA
    · change (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ) A = 1
      exact Units.ext (by
        simpa [Matrix.GeneralLinearGroup.val_det_apply] using
          CFSG.Open.StatedAPI.det_of_mem_statedSU hA)
  · intro A hA
    rw [Subgroup.mem_inf] at hA
    refine mem_statedSU_of_mem_unitaryFull h hQ hA.1 ?_
    have hdet : (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ) A = 1 := hA.2
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using congrArg Units.val hdet

omit [CharP E 2] in
theorem commutator_guFull_le_statedSU {k Q : ℕ} (hE : Nat.card E = Q ^ 2) :
    ⁅GUFull k Q E, GUFull k Q E⁆ ≤ StatedSU k Q E := by
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨f, hQf, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData E (q := Q) (by
    rw [← Nat.card_eq_fintype_card]; exact hE)
  have hSU := statedSU_eq_unitaryFull_inf_ker_det (m := k) hUF hQf
  rw [hSU]
  refine Subgroup.commutator_le.mpr ?_
  intro x hx y hy
  refine ⟨?_, ?_⟩
  · exact Subgroup.commutator_le_self (GUFull k Q E)
      (Subgroup.commutator_mem_commutator hx hy)
  · change (Matrix.GeneralLinearGroup.det : GL (Fin k) E →* Eˣ) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _

omit [CharP E 2] in
theorem commutator_guFull_eq_statedSU (hE : Nat.card E = 2 ^ 2) {k : ℕ} (hk : 4 ≤ k) :
    ⁅GUFull k 2 E, GUFull k 2 E⁆ = StatedSU k 2 E := by
  refine le_antisymm (commutator_guFull_le_statedSU (Q := 2) (by simpa using hE)) ?_
  have hqs := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := 1) (F := E) (n := k) (by simpa using hE) (by omega)
    (by rintro ⟨rfl, -⟩; omega)).1
  have hperf : commutator ↥(StatedSU k 2 E) = ⊤ := Group.isPerfect_def.mp hqs.1
  have hsu_eq : ⁅StatedSU k 2 E, StatedSU k 2 E⁆ = StatedSU k 2 E := by
    rw [← Subgroup.map_subtype_commutator (StatedSU k 2 E), hperf, Subgroup.map_top,
      Subgroup.range_subtype]
  calc
    StatedSU k 2 E = ⁅StatedSU k 2 E, StatedSU k 2 E⁆ := hsu_eq.symm
    _ ≤ ⁅GUFull k 2 E, GUFull k 2 E⁆ :=
      Subgroup.commutator_mono
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU)
        (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU)

private noncomputable def derivedEquiv {B : Subgroup G} {k : ℕ}
    (e : ↥B ≃* ↥(GUFull k 2 E)) :
    ↥⁅B, B⁆ ≃* ↥⁅GUFull k 2 E, GUFull k 2 E⁆ :=
  let c₁ : ↥⁅B, B⁆ ≃* ↥(commutator ↥B) :=
    (((commutator ↥B).equivMapOfInjective B.subtype B.subtype_injective).trans
      (MulEquiv.subgroupCongr B.map_subtype_commutator)).symm
  let c₂ : ↥(commutator ↥B) ≃* ↥(commutator ↥(GUFull k 2 E)) :=
    ((commutator ↥B).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.surjective]))
  let c₃ : ↥(commutator ↥(GUFull k 2 E)) ≃* ↥⁅GUFull k 2 E, GUFull k 2 E⁆ :=
    ((commutator ↥(GUFull k 2 E)).equivMapOfInjective (GUFull k 2 E).subtype
      (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (GUFull k 2 E)))
  c₁.trans (c₂.trans c₃)

private theorem rawDatum_unitaryLabel_commutator {k : ℕ} {E : Type} [Field E] [Finite E]
    {G : Type} [Group G] {B : Subgroup G}
    (hE : Nat.card E = (2 ^ 1) ^ 2) (hk : 1 ≤ k)
    (hqs : CFSG.IsQuasisimple ↥(LargeEvenSUGroup (Fin k) E (2 ^ 1)))
    (hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin k) E (2 ^ 1)) =
      (LargeEvenScalars (Fin k) E).subgroupOf (LargeEvenSUGroup (Fin k) E (2 ^ 1)))
    (φ : ↥⁅B, B⁆ ≃* ↥(LargeEvenSUGroup (Fin k) E (2 ^ 1))) :
    LargeEvenRawDatumLegacy (⟨.twA, k - 1, 1⟩ : LargeEvenLabel)
      (fun R _ _I _F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ _θ : ↥⁅B, B⁆ ⧸ Subgroup.center ↥⁅B, B⁆ ≃* R,
          (⟨.twA, k - 1, 1⟩ : LargeEvenLabel) = ⟨.twA, k - 1, 1⟩) := by
  simp only [CFSG.Assembly.LargeEvenRawDatumLegacy]
  rw [Nat.sub_add_cancel hk]
  refine ⟨E, inferInstance, inferInstance, hE, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · have : IsSimpleGroup (↥(LargeEvenSUGroup (Fin k) E (2 ^ 1)) ⧸
        Subgroup.center ↥(LargeEvenSUGroup (Fin k) E (2 ^ 1))) := hqs.2.1
    exact (QuotientGroup.quotientMulEquivOfEq hcenter).symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hqs.2.2
    refine ⟨(QuotientGroup.quotientMulEquivOfEq hcenter) a,
      (QuotientGroup.quotientMulEquivOfEq hcenter) b, ?_⟩
    intro h
    apply hab
    have h' := congrArg (QuotientGroup.quotientMulEquivOfEq hcenter).symm h
    rw [MulEquiv.map_mul, MulEquiv.map_mul] at h'
    rwa [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h'
  · refine ⟨(QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).trans
      (QuotientGroup.quotientMulEquivOfEq hcenter), trivial⟩

omit [CharP E 2] in
theorem largeEvenMarking_commutator_of_mulEquiv_guFull (hE : Nat.card E = 2 ^ 2)
    {B : Subgroup G} {k : ℕ} (hk : 4 ≤ k) (e : ↥B ≃* ↥(GUFull k 2 E)) :
    CFSG.StandardType.LargeEvenMarking ↥⁅B, B⁆
      (fun lab _ _ _ _ _ => lab = (⟨.twA, k - 1, 1⟩ : LargeEvenLabel)) := by
  let φ : ↥⁅B, B⁆ ≃* ↥(StatedSU k 2 E) :=
    (derivedEquiv e).trans (MulEquiv.subgroupCongr (commutator_guFull_eq_statedSU hE hk))
  have hqs := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := 1) (F := E) (n := k) (by simpa using hE) (by omega)
    (by rintro ⟨rfl, -⟩; omega))
  have hperfSU : Group.IsPerfect ↥(StatedSU k 2 E) := hqs.1.1
  have hperf : commutator ↥⁅B, B⁆ = ⊤ :=
    Group.isPerfect_def.mp
      (@Group.IsPerfect.ofSurjective ↥(StatedSU k 2 E) ↥⁅B, B⁆ _ _
        φ.symm.toMonoidHom hperfSU φ.symm.surjective)
  have hlab : LargeEvenInLambda2 (⟨.twA, k - 1, 1⟩ : LargeEvenLabel) := by
    simp only [LargeEvenInLambda2]
    refine ⟨by norm_num, ?_, ?_⟩
    · omega
    · intro hrank
      omega
  refine ⟨hperf, ⟨.twA, k - 1, 1⟩, hlab, ?_⟩
  have hqsSU : CFSG.IsQuasisimple ↥(LargeEvenSUGroup (Fin k) E (2 ^ 1)) := hqs.1
  have hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin k) E (2 ^ 1)) =
      (LargeEvenScalars (Fin k) E).subgroupOf (LargeEvenSUGroup (Fin k) E (2 ^ 1)) := by
    rw [CFSG.Assembly.largeEvenSUGroup_eq_statedSU k (2 ^ 1)]
    simpa [LargeEvenScalars] using hqs.2
  exact rawDatum_unitaryLabel_commutator (by simpa using hE) (by omega) hqsSU hcenter φ

private theorem isSolvable_statedSU_of_le_one {m Q : ℕ} {E : Type} [Field E] (hm : m ≤ 1) :
    Group.IsSolvable ↥(StatedSU m Q E) := by
  have : Subsingleton ↥(StatedSU m Q E) := by
    have := CFSG.LieType.SemisimpleCentralizers.Held.hct_subsingleton_statedSL_of_le_one
      (K := E) (d := m) hm
    refine ⟨fun x y => ?_⟩
    have h := Subsingleton.elim (α := ↥(CFSG.Open.StatedSL m E))
      ⟨x.1, CFSG.Open.StatedAPI.statedSU_le_statedSL m Q E x.2⟩
      ⟨y.1, CFSG.Open.StatedAPI.statedSU_le_statedSL m Q E y.2⟩
    exact Subtype.ext (congrArg (fun z : ↥(CFSG.Open.StatedSL m E) => (z : GL (Fin m) E)) h)
  infer_instance

private theorem isSolvable_statedSU_two_two {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = 2 ^ 2) : Group.IsSolvable ↥(StatedSU 2 2 E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (StatedSU 2 2 E) = 2 * (2 ^ 2 - 1) :=
    CFSG.RankThree.SubgroupLists.card_statedSU_two (K := E) (r := 2) (f := 1) (by
      rw [hE]; norm_num)
  exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
    (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [hcard]; norm_num)

private theorem isSolvable_statedSU_three_two {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = 2 ^ 2) : Group.IsSolvable ↥(StatedSU 3 2 E) := by
  have hcard' : Nat.card (StatedSU 3 (2 ^ 1) E) = 216 := by
    rw [CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two (F := E) (f := 1)
      (by rw [hE]; norm_num)]
    norm_num
  have hcard : Nat.card (StatedSU 3 2 E) = 216 := by simpa using hcard'
  exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
    (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [hcard]; norm_num)

theorem isSolvable_of_mulEquiv_guFull (hE : Nat.card E = 2 ^ 2)
    {B : Subgroup G} {k : ℕ} (hk : k ≤ 3) (e : ↥B ≃* ↥(GUFull k 2 E)) :
    Group.IsSolvable ↥B := by
  have hH_le : ⁅GUFull k 2 E, GUFull k 2 E⁆ ≤ StatedSU k 2 E :=
    commutator_guFull_le_statedSU (Q := 2) (by simpa using hE)
  have hSU_solv : Group.IsSolvable ↥(StatedSU k 2 E) := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · exact isSolvable_statedSU_of_le_one (by omega)
    · rcases Nat.lt_or_ge k 3 with hk3 | hk3
      · have hk2' : k = 2 := by omega
        subst hk2'
        exact isSolvable_statedSU_two_two hE
      · have hk3' : k = 3 := by omega
        subst hk3'
        exact isSolvable_statedSU_three_two hE
  have hH_solv : Group.IsSolvable ↥⁅GUFull k 2 E, GUFull k 2 E⁆ :=
    @Group.isSolvable_of_isSolvable_injective ↥⁅GUFull k 2 E, GUFull k 2 E⁆
      ↥(StatedSU k 2 E) _ _ (Subgroup.inclusion hH_le)
      (Subgroup.inclusion_injective hH_le) hSU_solv
  let c : ↥(commutator ↥(GUFull k 2 E)) ≃* ↥⁅GUFull k 2 E, GUFull k 2 E⁆ :=
    ((commutator ↥(GUFull k 2 E)).equivMapOfInjective (GUFull k 2 E).subtype
      (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator (GUFull k 2 E)))
  have hcomm_solv : Group.IsSolvable ↥(commutator ↥(GUFull k 2 E)) :=
    @Group.isSolvable_of_isSolvable_injective ↥(commutator ↥(GUFull k 2 E))
      ↥⁅GUFull k 2 E, GUFull k 2 E⁆ _ _ c.toMonoidHom c.injective hH_solv
  have hG_solv : Group.IsSolvable ↥(GUFull k 2 E) :=
    Group.isSolvable_commutator_iff.mp hcomm_solv
  exact @Group.isSolvable_of_isSolvable_injective ↥B ↥(GUFull k 2 E) _ _
    e.toMonoidHom e.injective hG_solv

theorem not_isComponentOf_commutator_of_mulEquiv_guFull (hE : Nat.card E = 2 ^ 2)
    {B : Subgroup G} {k : ℕ} (hk : k ≤ 3) (e : ↥B ≃* ↥(GUFull k 2 E)) (X : Subgroup G) :
    ¬ CFSG.Assembly.IsComponentOf X ⁅B, B⁆ := by
  have hB_solv : Group.IsSolvable ↥B := isSolvable_of_mulEquiv_guFull hE hk e
  have hcomm_solv : Group.IsSolvable ↥⁅B, B⁆ :=
    @Group.isSolvable_of_isSolvable_injective ↥⁅B, B⁆ ↥B _ _
      (Subgroup.inclusion (Subgroup.commutator_le_self B))
      (Subgroup.inclusion_injective (Subgroup.commutator_le_self B)) hB_solv
  exact CFSG.StandardType.ResU3Three.not_isComponentOf_of_isSolvable hcomm_solv

end CFSG.StandardType.GGQ2Frame.SpBlocks
