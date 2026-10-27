module

public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockDefs
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieGUDet
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResU3ThreeSolv
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple
public import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedSU StatedSL)
open CFSG.StandardType.ClassicalBlocks (GUFull)

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

theorem eq_statedSU_of_isComponentOf_unitaryFull {m Q : ℕ} {E : Type} [Field E] [Finite E]
    [CharP E 2] (hE : Nat.card E = Q ^ 2) {C : Subgroup (GL (Fin m) E)}
    (hC : IsComponentOf C (GUFull m Q E)) : C = StatedSU m Q E := by
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨f, hQf, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData E (q := Q) (by
    rw [← Nat.card_eq_fintype_card]; exact hE)
  have hSU := statedSU_eq_unitaryFull_inf_ker_det (m := m) hUF hQf
  have hC_le : C ≤ StatedSU m Q E := by
    intro c hc
    rw [hSU, Subgroup.mem_inf]
    refine ⟨hC.1 hc, ?_⟩
    have : Group.IsPerfect ↥C := ⟨hC.2.2.1⟩
    have hdet : (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ) c ∈
        MonoidHom.range ((Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ).comp
          C.subtype) := ⟨⟨c, hc⟩, rfl⟩
    have : Group.IsPerfect (MonoidHom.range ((Matrix.GeneralLinearGroup.det :
        GL (Fin m) E →* Eˣ).comp C.subtype)) := Group.IsPerfect.range _
    have : IsMulCommutative (MonoidHom.range ((Matrix.GeneralLinearGroup.det :
        GL (Fin m) E →* Eˣ).comp C.subtype)) := inferInstance
    have : Subsingleton (MonoidHom.range ((Matrix.GeneralLinearGroup.det :
        GL (Fin m) E →* Eˣ).comp C.subtype)) := inferInstance
    have htriv : (⟨_, hdet⟩ : MonoidHom.range ((Matrix.GeneralLinearGroup.det :
        GL (Fin m) E →* Eˣ).comp C.subtype)) = 1 := Subsingleton.elim _ _
    exact Subtype.ext_iff.mp htriv
  have hleGU : StatedSU m Q E ≤ GUFull m Q E :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.statedSU_le_statedGU
      (q := Q) (n := m) (L := E)
  have hCSU_asm : CFSG.Assembly.IsComponentOf (C.subgroupOf (StatedSU m Q E)) ⊤ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := (StatedSU m Q E).subtype) (StatedSU m Q E).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hC_le,
      Subgroup.map_top, Subgroup.range_subtype]
    exact hC.of_le_of_le hC_le hleGU
  have hCSU : CFSG.Open.IsComponentOf (C.subgroupOf (StatedSU m Q E)) ⊤ :=
    isComponentOf_iff_open.mp hCSU_asm
  have htop := CFSG.LieType.SemisimpleCentralizers.Held.hct_comp_top_statedSU hE
    (StatedSU m Q E) rfl (X := C.subgroupOf (StatedSU m Q E)) hCSU
  have hmap : (C.subgroupOf (StatedSU m Q E)).map (StatedSU m Q E).subtype = C := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hC_le]
  have htopmap : (⊤ : Subgroup ↥(StatedSU m Q E)).map (StatedSU m Q E).subtype =
      StatedSU m Q E := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  rw [← hmap, htop, htopmap]

private theorem guFull_eq_primeFormUnitary {m Q p f : ℕ} {E : Type} [Field E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E) (hQ : Q = p ^ f) :
    GUFull m Q E = CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (1 : Matrix (Fin m) (Fin m) E) := by
  rw [GUFull]
  have hset : {A : GL (Fin m) E | Matrix.transpose
      ((A : Matrix (Fin m) (Fin m) E).map (· ^ Q)) * (A : Matrix (Fin m) (Fin m) E) = 1} =
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
        (1 : Matrix (Fin m) (Fin m) E) : Set (GL (Fin m) E)) := by
    ext A
    rw [Set.mem_setOf_eq, SetLike.mem_coe,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary]
    have hmap : (A : Matrix (Fin m) (Fin m) E).map (· ^ Q) =
        (A : Matrix (Fin m) (Fin m) E).map h.bar := by
      ext i j
      rw [Matrix.map_apply, Matrix.map_apply, hQ, h.bar_apply]
    rw [hmap]
    simp only [Matrix.mul_one]
  rw [hset, Subgroup.closure_eq]

theorem guFull_subset_guSet {m Q p f : ℕ} {E : Type} [Field E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E) (hQ : Q = p ^ f) :
    (GUFull m Q E : Set (GL (Fin m) E)) ⊆ LargeEvenGUSet (Fin m) E Q := by
  intro A hA
  rw [guFull_eq_primeFormUnitary h hQ] at hA
  rw [SetLike.mem_coe,
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_primeFormUnitary] at hA
  refine ⟨1, one_ne_zero, one_pow _, ?_⟩
  rw [one_smul]
  rw [show (A : Matrix (Fin m) (Fin m) E).map (· ^ Q) =
      (A : Matrix (Fin m) (Fin m) E).map h.bar by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, hQ, h.bar_apply]]
  simpa only [Matrix.mul_one] using hA

theorem guFull_conj_mem_statedSU {m Q p f : ℕ} {E : Type} [Field E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E) (hQ : Q = p ^ f)
    {A : GL (Fin m) E} (hA : A ∈ GUFull m Q E) :
    ∀ g ∈ StatedSU m Q E, A * g * A⁻¹ ∈ StatedSU m Q E := by
  intro g hg
  have hSU := statedSU_eq_unitaryFull_inf_ker_det (m := m) h hQ
  have hg' := hSU ▸ hg
  rw [Subgroup.mem_inf] at hg'
  rw [hSU, Subgroup.mem_inf]
  refine ⟨(GUFull m Q E).mul_mem ((GUFull m Q E).mul_mem hA hg'.1)
    ((GUFull m Q E).inv_mem hA), ?_⟩
  change (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ) (A * g * A⁻¹) = 1
  have hdetg : (Matrix.GeneralLinearGroup.det : GL (Fin m) E →* Eˣ) g = 1 := hg'.2
  rw [map_mul, map_mul, map_inv, hdetg, mul_one, mul_inv_cancel]

theorem unitaryMarking_conj_mem_of_mem_unitaryFull {m Q p f : ℕ} {E : Type} [Field E]
    [Finite E] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E)
    (hQ : Q = p ^ f)
    (hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin m) E Q) =
      (LargeEvenScalars (Fin m) E).subgroupOf (LargeEvenSUGroup (Fin m) E Q))
    {ε : GL (Fin m) E} (hε : ε ∈ GUFull m Q E) :
    ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin m) E Q))
        (LargeEvenGUSet (Fin m) E Q),
      LargeEvenInduces (QuotientGroup.quotientMulEquivOfEq hcenter)
        (fun l l' : ↥(LargeEvenSUGroup (Fin m) E Q) =>
          (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ := by
  let SU := LargeEvenSUGroup (Fin m) E Q
  let Z := (LargeEvenScalars (Fin m) E).subgroupOf SU
  change ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk SU) (LargeEvenGUSet (Fin m) E Q),
    LargeEvenInduces (QuotientGroup.quotientMulEquivOfEq hcenter)
      (fun l l' : ↥SU => (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ
  have hcenter' : Subgroup.center ↥SU = Z := hcenter
  have : Z.Characteristic := hcenter' ▸ Subgroup.centerCharacteristic
  have hmem := guFull_conj_mem_statedSU (m := m) h hQ (A := ε⁻¹) ((GUFull m Q E).inv_mem hε)
  have hmem' := guFull_conj_mem_statedSU (m := m) h hQ (A := ε) hε
  let ψ : MulAut ↥SU :=
    { toFun := fun g => ⟨ε⁻¹ * (g : GL (Fin m) E) * ε, hmem g g.2⟩
      invFun := fun g => ⟨ε * (g : GL (Fin m) E) * ε⁻¹, hmem' g g.2⟩
      left_inv := fun g => Subtype.ext (by group)
      right_inv := fun g => Subtype.ext (by group)
      map_mul' := fun g₁ g₂ => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  let φ : MulAut (LargeEvenProj SU) :=
    QuotientGroup.congr Z Z ψ (Subgroup.characteristic_iff_map_eq.mp inferInstance ψ)
  refine ⟨φ, ?_, ?_⟩
  · refine ⟨ε⁻¹, guFull_subset_guSet h hQ ((GUFull m Q E).inv_mem hε), ?_⟩
    intro g g' hrel
    simp only [LargeEvenProjMk, φ]
    apply congrArg (QuotientGroup.mk' Z)
    refine Subtype.ext ?_
    change ε⁻¹ * (g : GL (Fin m) E) * ε = (g' : GL (Fin m) E)
    rw [hrel]
    group
  · intro g g' hrel
    simp only [QuotientGroup.quotientMulEquivOfEq_mk, φ]
    refine congrArg (QuotientGroup.mk' Z) (Subtype.ext ?_)
    exact hrel.symm

private theorem fieldFactorU_eq_of_semilin_statedSU {m f : ℕ} {E : Type} [Field E] [Finite E]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E) (hm : 3 ≤ m)
    (hq : ¬(m = 3 ∧ 2 ^ f = 2))
    {α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin m) E (2 ^ f)))}
    {B : GL (Fin m) E}
    (hB : B ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E))
    {τ : E ≃+* E}
    (hα : ∀ c : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)),
      ∃ v : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)),
        (v : GL (Fin m) E) = B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
          (c : GL (Fin m) E) * B⁻¹ ∧
        α (LargeEvenProjMk _ c) = LargeEvenProjMk _ v) :
    InndiagSU.fieldFactorU h hm hq α = τ := by
  classical
  let hd1 : 1 ≤ m := by omega
  let C0 : GL (Fin m) E := 1
  have hC0 : CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.IsPrimeFormGram C0 :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.isPrimeFormGram_one (K := E) (n := m)
  set Eα := MulAut.congr (InndiagSU.projEquiv h hd1) α with hEαdef
  let RHS : MulAut (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
      (C0 : Matrix (Fin m) (Fin m) E)) :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
        (C0 : Matrix (Fin m) (Fin m) E) ⟨B, hB⟩ *
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldHom h hC0 τ
  have hEα : Eα = RHS := by
    apply MulEquiv.ext
    intro y
    obtain ⟨q, rfl⟩ := (InndiagSU.projEquiv h hd1).surjective y
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨v, hv, hαv⟩ := hα c
    rw [hEαdef]
    change InndiagSU.projEquiv h hd1
        (α (LargeEvenProjMk (LargeEvenSUGroup (Fin m) E (2 ^ f)) c)) =
      RHS (InndiagSU.projEquiv h hd1
        (LargeEvenProjMk (LargeEvenSUGroup (Fin m) E (2 ^ f)) c))
    rw [hαv]
    change InndiagSU.projEquiv h hd1
        (v : LargeEvenProj (LargeEvenSUGroup (Fin m) E (2 ^ f))) =
      RHS (InndiagSU.projEquiv h hd1
        (c : LargeEvenProj (LargeEvenSUGroup (Fin m) E (2 ^ f))))
    rw [InndiagSU.projEquiv_mk h hd1, InndiagSU.projEquiv_mk h hd1]
    change ((⟨v, InndiagSU.largeEvenSUGroup_eq_gramSU (d := m) h ▸ v.2⟩ :
        CFSG.ClassicalGroups.UnitaryFlag.gramSU h
          ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)) :
        CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
          ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)) =
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
          ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) ⟨B, hB⟩
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldAut h hC0 τ
          (((⟨c, InndiagSU.largeEvenSUGroup_eq_gramSU (d := m) h ▸ c.2⟩ :
            CFSG.ClassicalGroups.UnitaryFlag.gramSU h
              ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E)) :
            CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormP h
              ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E))))
    rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldAut_mk,
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom_mk]
    congr 1
    exact Subtype.ext hv
  change CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor h hC0 hm hq Eα = τ
  rw [hEα]
  exact CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormFieldFactor_apply h hC0 hm hq
    ⟨B, hB⟩ τ

private theorem not_induced_unitary_statedSU_of_fieldAction {m f : ℕ} {E : Type} [Field E]
    [Finite E] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E)
    (hE : Nat.card E = (2 ^ f) ^ 2) (hm : 3 ≤ m) (h32 : (m, 2 ^ f) ≠ (3, 2))
    (hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) =
      (LargeEvenScalars (Fin m) E).subgroupOf (LargeEvenSUGroup (Fin m) E (2 ^ f)))
    (f' : MulAut ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)))
    {B : GL (Fin m) E} (hB : B ∈ GUFull m (2 ^ f) E) {τ : E ≃+* E}
    (hpoint : ∀ c : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)),
      (f' c : GL (Fin m) E) = B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
        (c : GL (Fin m) E) * B⁻¹)
    (hτ : τ ≠ 1) :
    ¬ ∃ φ ∈ Subgroup.closure
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin m) E (2 ^ f)))
        (LargeEvenGUSet (Fin m) E (2 ^ f))),
      LargeEvenInduces (QuotientGroup.quotientMulEquivOfEq hcenter)
        (fun j k : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) => k = f' j) φ := by
  classical
  let SU := LargeEvenSUGroup (Fin m) E (2 ^ f)
  let hd1 : 1 ≤ m := by omega
  have hq : ¬(m = 3 ∧ 2 ^ f = 2) := fun hh => h32 (by rw [hh.1, hh.2])
  have hB' : B ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      ((1 : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) := by
    have hg : GUFull m (2 ^ f) E = CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary
        h (CFSG.RankThree.PartOne.KCUnitaryModel.idGram E m) :=
      guFull_eq_primeFormUnitary (p := 2) (f := f) (Q := 2 ^ f) h rfl
    rw [hg] at hB
    simpa [CFSG.RankThree.PartOne.KCUnitaryModel.idGram] using hB
  let θ0 : SU ⧸ Subgroup.center SU ≃* LargeEvenProj SU :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  rintro ⟨φ, hφcl, hind⟩
  have hclosure : Subgroup.closure
      (LargeEvenMatConjImage (LargeEvenProjMk SU) (LargeEvenGUSet (Fin m) E (2 ^ f))) =
      InndiagSU.inndiagU h hd1 := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro ψ hψ
      exact (InndiagSU.mem_inndiagU h).mpr
        (InndiagSU.congr_mem_primeFormD h hd1 hE hψ)
    · intro ψ hψ
      exact Subgroup.subset_closure (InndiagSU.mem_conjImage_of_mem_inndiagU h hψ)
  have hφI : φ ∈ InndiagSU.inndiagU h hd1 := by
    rw [← hclosure]
    exact hφcl
  have hφker : InndiagSU.fieldFactorU h hm hq φ = 1 := by
    rw [← MonoidHom.mem_ker, InndiagSU.ker_fieldFactorU h hm hq]
    exact hφI
  have hφeq : φ = CFSG.StandardType.ggInducedAut θ0 f' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 := hind q (f' q) rfl
    have h2 := CFSG.StandardType.ggInducedAut_apply θ0 f' q
    exact h1.trans h2.symm
  have hαfield : InndiagSU.fieldFactorU h hm hq
      (CFSG.StandardType.ggInducedAut θ0 f') = τ := by
    refine fieldFactorU_eq_of_semilin_statedSU h hm hq hB' (τ := τ) ?_
    intro c
    refine ⟨f' c, hpoint c, ?_⟩
    have h1 := CFSG.StandardType.ggInducedAut_apply θ0 f' c
    rw [show θ0 (QuotientGroup.mk c) =
      (c : LargeEvenProj SU) from QuotientGroup.quotientMulEquivOfEq_mk _ c] at h1
    rw [show θ0 (QuotientGroup.mk (f' c)) =
      (f' c : LargeEvenProj SU) from QuotientGroup.quotientMulEquivOfEq_mk _ (f' c)] at h1
    exact h1
  apply hτ
  rw [← hαfield, ← hφeq]
  exact hφker

private theorem largeEvenRawDatum_unitaryLabel_statedSU_oneMarking {m f : ℕ} {E : Type}
    [Field E] [Finite E] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E)
    (hE : Nat.card E = (2 ^ f) ^ 2) (hm : 3 ≤ m) (h32 : (m, 2 ^ f) ≠ (3, 2))
    (hqs : CFSG.IsQuasisimple ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)))
    (hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) =
      (LargeEvenScalars (Fin m) E).subgroupOf (LargeEvenSUGroup (Fin m) E (2 ^ f)))
    (f' : MulAut ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)))
    {B : GL (Fin m) E} (hB : B ∈ GUFull m (2 ^ f) E) {τ : E ≃+* E}
    (hpoint : ∀ c : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)),
      (f' c : GL (Fin m) E) = B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
        (c : GL (Fin m) E) * B⁻¹)
    (hτ : τ ≠ 1) :
    LargeEvenRawDatumLegacy (⟨.twA, m - 1, f⟩ : LargeEvenLabel)
      (fun R _ I _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) ⧸
            Subgroup.center ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) ≃* R,
          ¬ ∃ φ ∈ Subgroup.closure I,
            LargeEvenInduces θ
              (fun j k : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) => k = f' j) φ) := by
  classical
  simp only [LargeEvenRawDatumLegacy]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  refine ⟨E, inferInstance, inferInstance, hE, ?_⟩
  let θ0 : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) ⧸
      Subgroup.center ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) ≃*
      LargeEvenProj (LargeEvenSUGroup (Fin m) E (2 ^ f)) :=
    QuotientGroup.quotientMulEquivOfEq hcenter
  refine ⟨?_, ?_, θ0, ?_⟩
  · have : IsSimpleGroup (↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) ⧸
        Subgroup.center ↥(LargeEvenSUGroup (Fin m) E (2 ^ f))) := hqs.2.1
    exact (QuotientGroup.quotientMulEquivOfEq hcenter).symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hqs.2.2
    refine ⟨(QuotientGroup.quotientMulEquivOfEq hcenter) a,
      (QuotientGroup.quotientMulEquivOfEq hcenter) b, ?_⟩
    intro h
    apply hab
    simpa using congrArg ((QuotientGroup.quotientMulEquivOfEq hcenter).symm) h
  · simpa [θ0] using
      not_induced_unitary_statedSU_of_fieldAction h hE hm h32 hcenter f' hB hpoint hτ

private theorem largeEvenRawDatum_unitaryLabel_statedSU {m Q p f : ℕ} {E : Type} [Field E]
    [Finite E] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E)
    (hQ : Q = p ^ f) (hE : Nat.card E = Q ^ 2) (h2f : 2 ^ f = Q) (hm : 3 ≤ m)
    (hqs : CFSG.IsQuasisimple ↥(LargeEvenSUGroup (Fin m) E Q))
    (hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin m) E Q) =
      (LargeEvenScalars (Fin m) E).subgroupOf (LargeEvenSUGroup (Fin m) E Q)) :
    CFSG.Assembly.LargeEvenRawDatumLegacy (⟨.twA, m - 1, f⟩ : LargeEvenLabel)
      (fun R _ I _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥(LargeEvenSUGroup (Fin m) E Q) ⧸
            Subgroup.center ↥(LargeEvenSUGroup (Fin m) E Q) ≃* R,
          GGChevStTag (⟨.twA, m - 1, f⟩ : LargeEvenLabel) ∧
          ∀ ε ∈ GUFull m Q E, ∃ φ ∈ I, LargeEvenInduces θ
            (fun l l' : ↥(LargeEvenSUGroup (Fin m) E Q) =>
              (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ) := by
  simp only [CFSG.Assembly.LargeEvenRawDatumLegacy]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m), h2f]
  refine ⟨E, inferInstance, inferInstance, hE, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · have : IsSimpleGroup (↥(LargeEvenSUGroup (Fin m) E Q) ⧸
        Subgroup.center ↥(LargeEvenSUGroup (Fin m) E Q)) := hqs.2.1
    exact (QuotientGroup.quotientMulEquivOfEq hcenter).symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := hqs.2.2
    refine ⟨(QuotientGroup.quotientMulEquivOfEq hcenter) a,
      (QuotientGroup.quotientMulEquivOfEq hcenter) b, ?_⟩
    intro h
    exact hab (by simpa using congrArg (QuotientGroup.quotientMulEquivOfEq hcenter).symm h)
  · refine ⟨QuotientGroup.quotientMulEquivOfEq hcenter, by simp [GGChevStTag], ?_⟩
    intro ε hε
    exact unitaryMarking_conj_mem_of_mem_unitaryFull h hQ hcenter hε

theorem unitaryLabel_data {m Q p f : ℕ} {E : Type} [Field E] [Finite E]
    (hQ : Q = p ^ f) (hE : Nat.card E = Q ^ 2) (hp2 : p = 2) (hm : 3 ≤ m)
    (h32 : (m, Q) ≠ (3, 2)) :
    2 ^ f = Q ∧ LargeEvenInLambda2 (⟨.twA, m - 1, f⟩ : LargeEvenLabel) := by
  have h2f : 2 ^ f = Q := by rw [hQ, hp2]
  have hQ2 : 2 ≤ Q := by
    have h1 : 1 < Nat.card E := Finite.one_lt_card
    rw [hE] at h1
    by_contra hlt
    have hle : Q ≤ 1 := by omega
    have hsq : Q ^ 2 ≤ 1 := by
      have := Nat.pow_le_pow_left hle 2
      simpa using this
    omega
  have hf1 : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    rw [hf0, pow_zero] at hQ
    omega
  refine ⟨h2f, ?_⟩
  simp only [LargeEvenInLambda2]
  refine ⟨hf1, by omega, ?_⟩
  intro hrank
  by_contra hf
  have hf1' : f = 1 := by omega
  rw [hf1', pow_one] at hQ
  exact h32 (by rw [show m = 3 by omega, hQ, hp2])

private theorem largeEvenMarking_oneMarking_unitary_statedSU_of_fieldAction {m f : ℕ} {E : Type}
    [Field E] [Finite E] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E)
    (hE : Nat.card E = (2 ^ f) ^ 2) (hm : 3 ≤ m) (h32 : (m, 2 ^ f) ≠ (3, 2))
    (f' : MulAut ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)))
    {B : GL (Fin m) E} (hB : B ∈ GUFull m (2 ^ f) E) {τ : E ≃+* E}
    (hpoint : ∀ c : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)),
      (f' c : GL (Fin m) E) = B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
        (c : GL (Fin m) E) * B⁻¹)
    (hτ : τ ≠ 1) :
    LargeEvenMarking ↥(LargeEvenSUGroup (Fin m) E (2 ^ f))
      (fun _ _ _ I _ θ => ¬ ∃ φ ∈ Subgroup.closure I,
        LargeEvenInduces θ
          (fun j k : ↥(LargeEvenSUGroup (Fin m) E (2 ^ f)) => k = f' j) φ) := by
  classical
  have hqs_pair := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := f) (F := E) (n := m) (by simpa using hE) hm h32
  let SU := LargeEvenSUGroup (Fin m) E (2 ^ f)
  have hqs : CFSG.IsQuasisimple ↥SU := hqs_pair.1
  have hcenter : Subgroup.center ↥SU =
      (LargeEvenScalars (Fin m) E).subgroupOf SU := by
    rw [show SU = CFSG.Open.StatedSU m (2 ^ f) E from
      CFSG.Assembly.largeEvenSUGroup_eq_statedSU m (2 ^ f)]
    simpa [LargeEvenScalars] using hqs_pair.2
  have hperf : commutator ↥SU = ⊤ := Group.isPerfect_def.mp hqs.1
  obtain ⟨-, hlab⟩ := unitaryLabel_data (Q := 2 ^ f) (p := 2) (f := f) rfl hE rfl hm h32
  refine ⟨hperf, ⟨.twA, m - 1, f⟩, hlab, ?_⟩
  exact largeEvenRawDatum_unitaryLabel_statedSU_oneMarking h hE hm h32 hqs hcenter f' hB hpoint hτ

theorem largeEvenMarking_oneMarking_statedSU_of_fieldAction {m Q : ℕ} {E : Type} [Field E]
    [Finite E] [CharP E 2] (hE : Nat.card E = Q ^ 2) (hm : 3 ≤ m)
    (h32 : (m, Q) ≠ (3, 2)) (f' : MulAut ↥(StatedSU m Q E))
    {B : GL (Fin m) E} (hB : B ∈ GUFull m Q E) {τ : E ≃+* E}
    (hpoint : ∀ c : ↥(StatedSU m Q E),
      (f' c : GL (Fin m) E) = B * CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.glAut τ
        (c : GL (Fin m) E) * B⁻¹)
    (hτ : τ ≠ 1) :
    LargeEvenMarking ↥(StatedSU m Q E)
      (fun _ _ _ I _ θ => ¬ ∃ φ ∈ Subgroup.closure I,
        LargeEvenInduces θ (fun j k : ↥(StatedSU m Q E) => k = f' j) φ) := by
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨f, hQf, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData E (q := Q) (by
    rw [← Nat.card_eq_fintype_card]; exact hE)
  have hp2 : ringChar E = 2 := CharP.eq E hUF.charP ‹CharP E 2›
  have hQ2 : Q = 2 ^ f := by rw [hQf, hp2]
  have hUF2 : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E := hp2 ▸ hUF
  have hE2 : Nat.card E = (2 ^ f) ^ 2 := by rw [hE, hQ2]
  have h32' : (m, 2 ^ f) ≠ (3, 2) := by simpa [hQ2] using h32
  clear hQf hUF hp2
  subst Q
  exact largeEvenMarking_oneMarking_unitary_statedSU_of_fieldAction hUF2 hE2 hm h32' f' hB hpoint hτ

private theorem largeEvenMarking_unitaryFull_statedSU {m Q p f : ℕ} {E : Type} [Field E]
    [Finite E] [hchar2 : CharP E 2]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f E)
    (hQ : Q = p ^ f) (hE : Nat.card E = Q ^ 2) (hm : 3 ≤ m)
    (h32 : (m, Q) ≠ (3, 2)) :
    LargeEvenMarking ↥(StatedSU m Q E) (fun lab _R _ I _ θ =>
      GGChevStTag lab ∧ ∀ ε ∈ GUFull m Q E,
        ∃ φ ∈ I, LargeEvenInduces θ
          (fun l l' : ↥(StatedSU m Q E) => (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ) := by
  let : Fact p.Prime := ⟨h.prime⟩
  have : CharP E p := h.charP
  let SU := LargeEvenSUGroup (Fin m) E Q
  have hSUeq : SU = StatedSU m Q E := rfl
  change LargeEvenMarking ↥SU (fun lab R _ I _ θ =>
    GGChevStTag lab ∧ ∀ ε ∈ GUFull m Q E,
      ∃ φ ∈ I, LargeEvenInduces θ
        (fun l l' : ↥SU => (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ)
  have hqs := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := p) (f := f) (F := E) (n := m) (by rw [← hQ]; exact hE) hm
    (by simpa [hQ] using h32))
  rw [← hQ, ← hSUeq] at hqs
  let Z := (LargeEvenScalars (Fin m) E).subgroupOf SU
  have hcenter : Subgroup.center ↥SU = Z := hqs.2
  have hperf : commutator ↥SU = ⊤ := Group.isPerfect_def.mp hqs.1.1
  have hp2 : p = 2 := CharP.eq E h.charP hchar2
  obtain ⟨h2f, hlab⟩ := unitaryLabel_data hQ hE hp2 hm h32
  refine ⟨hperf, ⟨.twA, m - 1, f⟩, hlab, ?_⟩
  exact largeEvenRawDatum_unitaryLabel_statedSU h hQ hE h2f hm hqs.1 hcenter

private theorem not_largeEvenMarking_of_isSolvable {L : Type} [Group L]
    (hs : Group.IsSolvable L) (h : LargeEvenMarking L (fun _ _ _ _ _ _ => True)) : False := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, hsimple, hna, θ, -⟩ :=
    largeEvenRawDatum_exists ((largeEvenRawDatum_legacy lab _).mpr hraw)
  have : IsSimpleGroup R := hsimple
  have : Nontrivial (L ⧸ Subgroup.center L) := θ.surjective.nontrivial
  have : Nontrivial L := (QuotientGroup.mk'_surjective (Subgroup.center L)).nontrivial
  have : Group.IsPerfect L := ⟨hcomm⟩
  exact Group.IsPerfect.not_isSolvable (G := L) hs

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

theorem isSolvable_statedSU_two_two {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = 2 ^ 2) : Group.IsSolvable ↥(StatedSU 2 2 E) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (StatedSU 2 2 E) = 2 * (2 ^ 2 - 1) :=
    CFSG.RankThree.SubgroupLists.card_statedSU_two (K := E) (r := 2) (f := 1) (by
      rw [hE]; norm_num)
  exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
    (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [hcard]; norm_num)

theorem isSolvable_statedSU_three_two {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = 2 ^ 2) : Group.IsSolvable ↥(StatedSU 3 2 E) := by
  have hcard' : Nat.card (StatedSU 3 (2 ^ 1) E) = 216 := by
    rw [CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two (F := E) (f := 1)
      (by rw [hE]; norm_num)]
    norm_num
  have hcard : Nat.card (StatedSU 3 2 E) = 216 := by simpa using hcard'
  exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
    (p := 2) (q := 3) (a := 3) (b := 3) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [hcard]; norm_num)

private theorem exists_statedClassicalModel_statedSU_two {Q f : ℕ} {E : Type} [Field E]
    [Finite E] [CharP E 2] (hQ : Q = 2 ^ f) (hE : Nat.card E = Q ^ 2) (hf : 2 ≤ f) :
    CFSG.Open.StatedClassicalModel
      (↥(StatedSU 2 Q E) ⧸ Subgroup.center ↥(StatedSU 2 Q E)) .PSL 2 2 f := by
  subst Q
  let F := CFSG.LieType.Steinberg.fixedSubfield E 2 f
  have hcardF : Nat.card F = 2 ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield (p := 2) (f := f) (F := E) (by simpa using hE)
  have h4 : 4 ≤ 2 ^ f := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hf
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 2 2 f := by
    refine ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩
    · intro hpair
      have h2 : 2 ^ f = 2 := (Prod.mk.inj hpair).2
      omega
    · intro hpair
      have h3 : 2 ^ f = 3 := (Prod.mk.inj hpair).2
      omega
  obtain ⟨e1⟩ := SURepair.nonempty_sl2_mulEquiv_unitarySU_two (K := E) (f := f) hE
  let eSU : ↥(StatedSU 2 (2 ^ f) E) ≃* ↥(CFSG.Open.StatedSL 2 F) :=
    e1.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F)
  let eZ : ↥(StatedSU 2 (2 ^ f) E) ⧸ Subgroup.center ↥(StatedSU 2 (2 ^ f) E) ≃*
      ↥(CFSG.Open.StatedSL 2 F) ⧸ Subgroup.center ↥(CFSG.Open.StatedSL 2 F) :=
    QuotientGroup.congr _ _ eSU (Subgroup.map_center_eq eSU)
  let e3 : ↥(CFSG.Open.StatedSL 2 F) ⧸ Subgroup.center ↥(CFSG.Open.StatedSL 2 F) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 F) :=
    QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq 2)
  exact ⟨hadm, F, inferInstance, inferInstance, hcardF, ⟨eZ.trans e3⟩⟩

private theorem exists_label_of_quasisimple_statedSU
    {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = Q ^ 2) (hq : CFSG.Assembly.IsQuasisimple ↥(StatedSU m Q E)) :
    ∃ f : ℕ, 1 ≤ f ∧ Q = 2 ^ f ∧
      ((m = 2 ∧ LargeEvenInLambda2 (⟨.A, 1, f⟩ : LargeEvenLabel) ∧
        GGHasLabel ⟨.A, 1, f⟩ (↥(StatedSU m Q E) ⧸ Subgroup.center ↥(StatedSU m Q E))) ∨
       (3 ≤ m ∧ LargeEvenInLambda2 (⟨.twA, m - 1, f⟩ : LargeEvenLabel) ∧
        GGHasLabel ⟨.twA, m - 1, f⟩
          (↥(StatedSU m Q E) ⧸ Subgroup.center ↥(StatedSU m Q E)))) := by
  let : Fintype E := Fintype.ofFinite E
  let : Group.IsPerfect ↥(StatedSU m Q E) := Group.isPerfect_def.mpr hq.1
  let : Nontrivial (↥(StatedSU m Q E) ⧸ Subgroup.center ↥(StatedSU m Q E)) :=
    hq.2.toNontrivial
  let : Nontrivial ↥(StatedSU m Q E) :=
    Function.Surjective.nontrivial
      (QuotientGroup.mk_surjective (s := Subgroup.center ↥(StatedSU m Q E)))
  have hnsol : ¬ Group.IsSolvable ↥(StatedSU m Q E) :=
    Group.IsPerfect.not_isSolvable ↥(StatedSU m Q E)
  by_cases hm1 : m ≤ 1
  · exact (hnsol (isSolvable_statedSU_of_le_one hm1)).elim
  obtain ⟨f, hQ, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData E (q := Q) (by
    rw [← Nat.card_eq_fintype_card]; exact hE)
  have hp2 : ringChar E = 2 := CharP.eq E hUF.charP (inferInstance : CharP E 2)
  rw [hp2] at hQ hUF
  have hf : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    have hcard1 : Nat.card E = 1 := by simpa [hQ, hf0] using hE
    have := Finite.one_lt_card (α := E)
    omega
  by_cases hm3 : 3 ≤ m
  · by_cases h32 : (m, Q) = (3, 2)
    · have hsol : Group.IsSolvable ↥(StatedSU m Q E) := by
        rw [(Prod.mk.inj h32).1, (Prod.mk.inj h32).2]
        exact isSolvable_statedSU_three_two (by simpa [(Prod.mk.inj h32).2] using hE)
      exact (hnsol hsol).elim
    obtain ⟨r, hmr⟩ : ∃ r : ℕ, m = r + 1 := ⟨m - 1, by omega⟩
    subst m
    subst Q
    obtain ⟨-, hΛ⟩ := unitaryLabel_data (p := 2) (f := f) rfl hE rfl hm3 h32
    have hqs := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
      (p := 2) (f := f) (F := E) (n := r + 1) hE hm3 h32
    have hcenter : Subgroup.center ↥(LargeEvenSUGroup (Fin (r + 1)) E (2 ^ f)) =
        (LargeEvenScalars (Fin (r + 1)) E).subgroupOf
          (LargeEvenSUGroup (Fin (r + 1)) E (2 ^ f)) := hqs.2
    refine ⟨f, hf, rfl, Or.inr ⟨hm3, hΛ, ?_⟩⟩
    have hrawLeg := largeEvenRawDatum_unitaryLabel_statedSU hUF rfl hE rfl hm3 hqs.1 hcenter
    have hraw := (largeEvenRawDatum_legacy (⟨.twA, r + 1 - 1, f⟩ : LargeEvenLabel) _).2 hrawLeg
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨_, _, θ, _⟩
    exact ⟨θ⟩
  · have hm2 : m = 2 := by omega
    subst m
    have hf2 : 2 ≤ f := by
      by_contra h
      have hf1 : f = 1 := by omega
      have hQ2 : Q = 2 := by simpa [hf1] using hQ
      have hsol : Group.IsSolvable ↥(StatedSU 2 Q E) := by
        rw [hQ2]
        exact isSolvable_statedSU_two_two (by simpa [hQ2] using hE)
      exact hnsol hsol
    obtain ⟨-, k, hk, hkfin, hkcard, ⟨eModel⟩⟩ :=
      exists_statedClassicalModel_statedSU_two hQ hE hf2
    let : Field k := hk
    let : Finite k := hkfin
    let eProj : StatedSL 2 k ⧸ Subgroup.center (StatedSL 2 k) ≃*
        CFSG.Open.StatedProj (StatedSL 2 k) :=
      QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq 2)
    let θ : ↥(StatedSU 2 Q E) ⧸ Subgroup.center ↥(StatedSU 2 Q E) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin 2) k) :=
      eModel.trans (eProj.symm.trans statedSLQuotEquivLargeEvenProj)
    have hΛ : LargeEvenInLambda2 (⟨.A, 1, f⟩ : LargeEvenLabel) :=
      ⟨by omega, le_rfl, fun _ => hf2⟩
    exact ⟨f, hf, hQ, Or.inl ⟨rfl, hΛ,
      ggHasLabel_linear_of_supplied (by omega) hkcard θ⟩⟩

theorem exists_unitary_label_of_isComponentOf_iso_unitaryFull
    {H : Type} [Group H] {F : Subgroup H} {m Q : ℕ} {E : Type}
    [Field E] [Finite E] [CharP E 2] (hE : Nat.card E = Q ^ 2)
    (e : ↥F ≃* ↥(GUFull m Q E)) {C : Subgroup H} (hC : IsComponentOf C F) :
    ∃ f : ℕ, 1 ≤ f ∧ Q = 2 ^ f ∧
      ((m = 2 ∧ LargeEvenInLambda2 (⟨.A, 1, f⟩ : LargeEvenLabel) ∧
        GGHasLabel ⟨.A, 1, f⟩ (↥C ⧸ Subgroup.center ↥C)) ∨
       (3 ≤ m ∧ LargeEvenInLambda2 (⟨.twA, m - 1, f⟩ : LargeEvenLabel) ∧
        GGHasLabel ⟨.twA, m - 1, f⟩ (↥C ⧸ Subgroup.center ↥C))) := by
  let φ : ↥F →* GL (Fin m) E := (GUFull m Q E).subtype.comp e.toMonoidHom
  have hinj : Function.Injective φ := (GUFull m Q E).subtype_injective.comp e.injective
  have hcomp : CFSG.IsComponent (C.subgroupOf F) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hC.1).1 hC
  have hmapped : CFSG.IsComponent ((C.subgroupOf F).map e.toMonoidHom) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent e hcomp
  have htop : IsComponentOf ((C.subgroupOf F).map e.toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native _).2 hmapped
  have hmap : IsComponentOf (((C.subgroupOf F).map e.toMonoidHom).map
      (GUFull m Q E).subtype) ((⊤ : Subgroup ↥(GUFull m Q E)).map (GUFull m Q E).subtype) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := (GUFull m Q E).subtype) (GUFull m Q E).subtype_injective).2 htop
  have hCφ : IsComponentOf ((C.subgroupOf F).map φ) (GUFull m Q E) := by
    simpa only [Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype, φ] using hmap
  have heq := eq_statedSU_of_isComponentOf_unitaryFull hE hCφ
  let ec : ↥C ≃* ↥(StatedSU m Q E) :=
    (Subgroup.subgroupOfEquivOfLe hC.1).symm.trans
      (((C.subgroupOf F).equivMapOfInjective φ hinj).trans (MulEquiv.subgroupCongr heq))
  let eQ : ↥C ⧸ Subgroup.center ↥C ≃*
      ↥(StatedSU m Q E) ⧸ Subgroup.center ↥(StatedSU m Q E) :=
    QuotientGroup.congr _ _ ec (Subgroup.map_center_eq (f := ec))
  have htransport : ∀ lab : LargeEvenLabel,
      GGHasLabel lab (↥(StatedSU m Q E) ⧸ Subgroup.center ↥(StatedSU m Q E)) →
        GGHasLabel lab (↥C ⧸ Subgroup.center ↥C) := by
    intro lab h
    unfold GGHasLabel at h ⊢
    refine largeEvenRawDatum_mono ?_ h
    rintro R _ I F ⟨θ⟩
    exact ⟨eQ.trans θ⟩
  obtain ⟨f, hf, hQ, hlabel⟩ :=
    exists_label_of_quasisimple_statedSU hE (hC.2.2.of_mulEquiv ec.symm)
  refine ⟨f, hf, hQ, ?_⟩
  rcases hlabel with ⟨hm, hΛ, hh⟩ | ⟨hm, hΛ, hh⟩
  · exact Or.inl ⟨hm, hΛ, htransport _ hh⟩
  · exact Or.inr ⟨hm, hΛ, htransport _ hh⟩

private theorem exists_heldGU_conj_of_mem_unitaryFull_two {Q f : ℕ} {E : Type} [Field E]
    [Finite E] [CharP E 2] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E)
    (hQ : Q = 2 ^ f) (hE : Nat.card E = Q ^ 2) {ε : GL (Fin 2) E}
    (hε : ε ∈ GUFull 2 Q E) :
    ∃ (τ : E ≃+* E) (hτ : ∀ x, τ (τ x) = x),
      (∀ x, τ x = x ^ Q) ∧ ∃ A ∈ CFSG.LieType.SemisimpleCentralizers.Held.heldGU 2 E τ hτ,
        ∀ g : GL (Fin 2) E, A * g * A⁻¹ = ε * g * ε⁻¹ := by
  have hK : Nat.card E = (2 ^ f) ^ 2 := by
    rw [← hQ]
    exact hE
  obtain ⟨τ, hτq, hτ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv (K := E) (n := f) hK
  have hτQ : ∀ x : E, τ x = x ^ Q := by
    intro x
    rw [hQ]
    exact hτq x
  have hεgu : ε ∈ LargeEvenGUSet (Fin 2) E Q := guFull_subset_guSet h hQ hε
  have hεgu' : ε ∈ LargeEvenGUSet (Fin 2) E (2 ^ f) := by
    rwa [hQ] at hεgu
  obtain ⟨A, hAheld, hAconj⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_heldGU_of_GUSet
      (K := E) (d := 2) (n := f) hτq hK hτ ε hεgu'
  exact ⟨τ, hτ, hτQ, A, hAheld, hAconj⟩

private theorem det_pow_card_add_one_of_mem_heldGU {Q : ℕ} {E : Type} [Field E]
    {τ : E ≃+* E} {hτ : ∀ x, τ (τ x) = x} {A : GL (Fin 2) E}
    (hA : A ∈ CFSG.LieType.SemisimpleCentralizers.Held.heldGU 2 E τ hτ)
    (hτQ : ∀ x, τ x = x ^ Q) :
    ((Matrix.GeneralLinearGroup.det A : E)) ^ (Q + 1) = 1 := by
  have hA'm : Matrix.transpose ((A : Matrix (Fin 2) (Fin 2) E).map τ) *
      (A : Matrix (Fin 2) (Fin 2) E) = 1 :=
    CFSG.LieType.SemisimpleCentralizers.Held.mem_heldGU.mp hA
  have h1 := congrArg Matrix.det hA'm
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
  have hmapdet : ((A : Matrix (Fin 2) (Fin 2) E).map τ).det =
      ((A : Matrix (Fin 2) (Fin 2) E).det) ^ Q := by
    have h2 : τ ((A : Matrix (Fin 2) (Fin 2) E).det) =
        ((A : Matrix (Fin 2) (Fin 2) E).map τ).det := by
      simpa using RingHom.map_det τ.toRingHom (A : Matrix (Fin 2) (Fin 2) E)
    rw [hτQ] at h2
    exact h2.symm
  rw [hmapdet, ← pow_succ] at h1
  exact h1

private theorem exists_scalar_sq_eq_inv_det {Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    {d : Eˣ} (hdQ : ((d : E)) ^ (Q + 1) = 1) :
    ∃ c : E, c ≠ 0 ∧ c ^ 2 = ((d : E))⁻¹ ∧ c ^ (Q + 1) = 1 := by
  have hsurj : Function.Surjective (fun x : E => x ^ 2) :=
    Finite.injective_iff_surjective.mp (CharTwo.sq_injective (R := E))
  obtain ⟨c, hc⟩ := hsurj ((d : E)⁻¹)
  change c ^ 2 = ((d : E))⁻¹ at hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : (0 : E) = ((d : E))⁻¹ := by simpa using hc
    exact (inv_ne_zero d.ne_zero) h0.symm
  have hcQ : c ^ (Q + 1) = 1 := by
    have hsq : (c ^ (Q + 1)) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm (Q + 1) 2, pow_mul, hc, inv_pow, hdQ, inv_one]
    exact CharTwo.sq_injective (by simpa using hsq)
  exact ⟨c, hc0, hc, hcQ⟩

private theorem scalar_mul_mem_statedSU_of_mem_heldGU {Q : ℕ} {E : Type} [Field E] [Finite E]
    [CharP E 2] {τ : E ≃+* E} {hτ : ∀ x, τ (τ x) = x} {A : GL (Fin 2) E}
    (hA : A ∈ CFSG.LieType.SemisimpleCentralizers.Held.heldGU 2 E τ hτ)
    (hτQ : ∀ x, τ x = x ^ Q) {c : E} (hc0 : c ≠ 0) (hcQ : c ^ (Q + 1) = 1)
    (hcdet : c ^ 2 * ((Matrix.GeneralLinearGroup.det A : E)) = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) * A ∈ StatedSU 2 Q E := by
  let s : GL (Fin 2) E := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0)
  let B : GL (Fin 2) E := s * A
  have hval : ((B : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      c • (A : Matrix (Fin 2) (Fin 2) E) := by
    rw [show B = s * A from rfl, Units.val_mul,
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.val_scalar_gl', Matrix.smul_mul, Matrix.one_mul]
    rfl
  have hA'm : Matrix.transpose ((A : Matrix (Fin 2) (Fin 2) E).map τ) *
      (A : Matrix (Fin 2) (Fin 2) E) = 1 :=
    CFSG.LieType.SemisimpleCentralizers.Held.mem_heldGU.mp hA
  have hA'Q : Matrix.transpose ((A : Matrix (Fin 2) (Fin 2) E).map (fun x : E => x ^ Q)) *
      (A : Matrix (Fin 2) (Fin 2) E) = 1 := by
    rw [show (fun x : E => x ^ Q) = ⇑τ from funext fun x => (hτQ x).symm]
    exact hA'm
  have hBheld : B ∈ CFSG.LieType.SemisimpleCentralizers.Held.heldGU 2 E τ hτ := by
    rw [CFSG.LieType.SemisimpleCentralizers.Held.mem_heldGU, hval, show (⇑τ) = fun x : E => x ^ Q
      from funext hτQ, CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.map_smul_pow,
      Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hA'Q]
    rw [smul_smul, show c ^ Q * c = 1 by rw [← pow_succ, hcQ], one_smul]
  have hdetB : ((B : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).det = 1 := by
    rw [hval, Matrix.det_smul, Fintype.card_fin]
    show c ^ 2 * ((Matrix.GeneralLinearGroup.det A : E)) = 1
    exact hcdet
  rw [← CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU
    (a := 2) (Q := Q) (M := E) (τ := τ) (hτ := hτ) hτQ]
  refine ⟨hBheld, ?_⟩
  change B ∈ CFSG.Open.StatedSL 2 E
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
  exact hdetB

private lemma conj_scalar_mul_eq_conj {E : Type} [Field E] {A : GL (Fin 2) E} {c : E}
    (hc0 : c ≠ 0) (l : GL (Fin 2) E) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) * A)⁻¹ * l *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) * A) = A⁻¹ * l * A := by
  let s : GL (Fin 2) E := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0)
  have hs : ∀ x : GL (Fin 2) E, s * x = x * s := fun x =>
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.scalar_comm_gl (Units.mk0 c hc0) x
  have h1 : s⁻¹ * l * s = l := by
    calc s⁻¹ * l * s = s⁻¹ * (l * s) := by group
      _ = s⁻¹ * (s * l) := by rw [← hs l]
      _ = l := by group
  calc (s * A)⁻¹ * l * (s * A) = A⁻¹ * (s⁻¹ * l * s) * A := by group
    _ = A⁻¹ * l * A := by rw [h1]

private theorem exists_inner_of_mem_unitaryFull_two {Q f : ℕ} {E : Type} [Field E] [Finite E]
    [CharP E 2] (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E)
    (hQ : Q = 2 ^ f) (hE : Nat.card E = Q ^ 2) {ε : GL (Fin 2) E}
    (hε : ε ∈ GUFull 2 Q E) :
    ∃ u ∈ StatedSU 2 Q E, ∀ l ∈ StatedSU 2 Q E,
      ε⁻¹ * l * ε = u⁻¹ * l * u := by
  obtain ⟨τ, hτ, hτQ, A, hAheld, hAconj⟩ :=
    exists_heldGU_conj_of_mem_unitaryFull_two h hQ hE hε
  have hdQ := det_pow_card_add_one_of_mem_heldGU hAheld hτQ
  obtain ⟨c, hc0, hc2, hcQ⟩ := exists_scalar_sq_eq_inv_det hdQ
  have hcdet : c ^ 2 * ((Matrix.GeneralLinearGroup.det A : E)) = 1 := by
    rw [hc2]
    exact inv_mul_cancel₀ (Matrix.GeneralLinearGroup.det A).ne_zero
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) * A,
    scalar_mul_mem_statedSU_of_mem_heldGU hAheld hτQ hc0 hcQ hcdet, ?_⟩
  intro l hl
  rw [conj_scalar_mul_eq_conj hc0 l]
  have hAl : A⁻¹ * l * A = ε⁻¹ * l * ε := by
    have h := hAconj (A⁻¹ * l * A)
    have hleft : A * (A⁻¹ * l * A) * A⁻¹ = l := by
      simp only [mul_assoc, mul_inv_cancel, mul_inv_cancel_left, mul_one]
    rw [hleft] at h
    calc A⁻¹ * l * A = ε⁻¹ * (ε * (A⁻¹ * l * A) * ε⁻¹) * ε := by
          simp only [mul_assoc, inv_mul_cancel, inv_mul_cancel_left, mul_one]
      _ = ε⁻¹ * l * ε := by rw [← h]
  exact hAl.symm

private theorem ggE0Concl_statedSU_two {Q f : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E) (hQ : Q = 2 ^ f)
    (hE : Nat.card E = Q ^ 2) (hQne : Q ≠ 2)
    (hm : LargeEvenMarking ↥(StatedSU 2 Q E) (fun _ _ _ _ _ _ => True)) :
    LargeEvenMarking ↥(StatedSU 2 Q E) (fun lab _R _ I _ θ =>
      GGChevStTag lab ∧ ∀ ε ∈ GUFull 2 Q E,
        ∃ φ ∈ I, LargeEvenInduces θ
          (fun l l' : ↥(StatedSU 2 Q E) => (l' : GL (Fin 2) E) = ε⁻¹ * l * ε) φ) := by
  have hf : 2 ≤ f := by
    by_contra hf
    have hf0 : f = 0 ∨ f = 1 := by omega
    rcases hf0 with rfl | rfl
    · rw [pow_zero] at hQ
      have h1 : 1 < Nat.card E := Finite.one_lt_card
      rw [hE, hQ] at h1
      norm_num at h1
    · rw [pow_one] at hQ
      exact hQne hQ
  have hqs : CFSG.IsQuasisimple ↥(StatedSU 2 Q E) := by
    have hqs := SURepair.isQuasisimple_unitarySU_two (K := E) (f := f) h hf
    rwa [show CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 f E 2 = StatedSU 2 Q E from by
      rw [CFSG.ClassicalGroups.UnitaryFlag.unitarySU, hQ]] at hqs
  have hqsA : CFSG.Assembly.IsQuasisimple ↥(StatedSU 2 Q E) :=
    ⟨Group.isPerfect_def.mp hqs.1, hqs.2.1⟩
  have hmodel := exists_statedClassicalModel_statedSU_two hQ hE hf
  have hmark := largeEvenMarking_inn_of_statedClassicalModel hqsA hmodel
  have hinn : ∀ ε ∈ GUFull 2 Q E, ∃ c ∈ StatedSU 2 Q E,
      ∀ l ∈ StatedSU 2 Q E, ε⁻¹ * l * ε = c⁻¹ * l * c :=
    fun ε hε => exists_inner_of_mem_unitaryFull_two h hQ hE hε
  exact (ggE0Concl_of_inner hinn hmark).2 hm

theorem ggE0Concl_unitaryFull_statedSU {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = Q ^ 2) : GGE0Concl (GUFull m Q E) (StatedSU m Q E) := by
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨f, hQf, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData E (q := Q) (by
    rw [← Nat.card_eq_fintype_card]; exact hE)
  have hp2 : ringChar E = 2 := CharP.eq E hUF.charP ‹CharP E 2›
  have hQ2 : Q = 2 ^ f := by rw [hQf, hp2]
  have hUF2 : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E := hp2 ▸ hUF
  refine ⟨?_, ?_⟩
  · rw [Subgroup.le_normalizer_iff]
    intro ε hε g hg
    exact guFull_conj_mem_statedSU hUF hQf hε g hg
  · intro hm
    by_cases hm1 : m ≤ 1
    · exact (not_largeEvenMarking_of_isSolvable (isSolvable_statedSU_of_le_one hm1) hm).elim
    have hm2 : 2 ≤ m := by omega
    by_cases hm2eq : m = 2
    · subst hm2eq
      by_cases hQsmall : Q = 2
      · subst hQsmall
        exact (not_largeEvenMarking_of_isSolvable (isSolvable_statedSU_two_two hE) hm).elim
      · exact ggE0Concl_statedSU_two hUF2 hQ2 hE hQsmall hm
    · have hm3 : 3 ≤ m := by omega
      by_cases h32 : m = 3 ∧ Q = 2
      · obtain ⟨rfl, rfl⟩ := h32
        exact (not_largeEvenMarking_of_isSolvable (isSolvable_statedSU_three_two hE) hm).elim
      · refine largeEvenMarking_unitaryFull_statedSU hUF hQf hE hm3 ?_
        rintro ⟨rfl, rfl⟩
        exact h32 ⟨rfl, rfl⟩

theorem largeEvenMarking_of_isComponentOf_unitaryFull {m Q : ℕ} {E : Type} [Field E] [Finite E]
    [CharP E 2] (hE : Nat.card E = Q ^ 2) {C : Subgroup (GL (Fin m) E)}
    (hC : IsComponentOf C (GUFull m Q E)) :
    LargeEvenMarking C (fun _ _ _ _ _ _ => True) := by
  obtain rfl := eq_statedSU_of_isComponentOf_unitaryFull hE hC
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨f, hQf, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData E (q := Q) (by
    rw [← Nat.card_eq_fintype_card]; exact hE)
  have hp2 : ringChar E = 2 := CharP.eq E hUF.charP ‹CharP E 2›
  have hQ2 : Q = 2 ^ f := by rw [hQf, hp2]
  have hUF2 : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f E := hp2 ▸ hUF
  by_cases hm1 : m ≤ 1
  · exact (ResU3Three.not_isSolvable_of_isQuasisimple hC.2.2
      (isSolvable_statedSU_of_le_one hm1)).elim
  by_cases hm2 : m = 2
  · subst m
    by_cases hQsmall : Q = 2
    · rw [hQsmall] at hC hE ⊢
      exact (ResU3Three.not_isSolvable_of_isQuasisimple hC.2.2
        (isSolvable_statedSU_two_two hE)).elim
    · have hf : 2 ≤ f := by
        rcases Nat.lt_or_ge f 2 with hlt | hge
        · have hf0 : f = 0 ∨ f = 1 := by omega
          rcases hf0 with rfl | rfl
          · rw [pow_zero] at hQ2
            have h1 : 1 < Nat.card E := Finite.one_lt_card
            rw [hE, hQ2] at h1
            norm_num at h1
          · rw [pow_one] at hQ2
            exact (hQsmall hQ2).elim
        · exact hge
      have hmodel := exists_statedClassicalModel_statedSU_two hQ2 hE hf
      exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
        (largeEvenMarking_inn_of_statedClassicalModel hC.2.2 hmodel)
  · have hm3 : 3 ≤ m := by omega
    by_cases h32 : m = 3 ∧ Q = 2
    · obtain ⟨rfl, rfl⟩ := h32
      exact (ResU3Three.not_isSolvable_of_isQuasisimple hC.2.2
        (isSolvable_statedSU_three_two hE)).elim
    · refine largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
        (largeEvenMarking_unitaryFull_statedSU hUF2 hQ2 hE hm3 ?_)
      rintro ⟨rfl, rfl⟩
      exact h32 ⟨rfl, rfl⟩

theorem ggE0Concl_unitaryFull {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = Q ^ 2) (C : Subgroup (GL (Fin m) E))
    (hC : IsComponentOf C (GUFull m Q E)) : GGE0Concl (GUFull m Q E) C := by
  rw [eq_statedSU_of_isComponentOf_unitaryFull hE hC]
  exact ggE0Concl_unitaryFull_statedSU hE

end CFSG.StandardType
