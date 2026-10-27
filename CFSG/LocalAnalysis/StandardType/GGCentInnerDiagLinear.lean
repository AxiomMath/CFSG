module

public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagConcl
public import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSL
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNILinOuter

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open (StatedSL)

theorem eq_statedSL_of_isComponentOf_top {m : ℕ} {E : Type} [Field E] [Finite E]
    {C : Subgroup (GL (Fin m) E)} (hC : IsComponentOf C ⊤) : C = StatedSL m E := by
  have hperf : commutator ↥C = ⊤ := hC.2.2.1
  have hmap : ⁅C, C⁆ = (commutator ↥C).map C.subtype := by
    have h := (Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥C)) (H₂ := ⊤) C.subtype).symm
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    exact h
  have hcommCL : ⁅C, C⁆ = C := by
    rw [hmap, hperf, Subgroup.map_top, Subgroup.range_subtype]
  have hCSL : C ≤ StatedSL m E := by
    rw [← hcommCL]
    refine (Subgroup.commutator_mono hC.1 hC.1).trans ?_
    exact Subgroup.commutator_le.mpr fun a _ b _ =>
      CFSG.LieType.SemisimpleCentralizers.Held.commutatorElement_mem_statedSL a b
  have hcomp : CFSG.Assembly.IsComponentOf C (StatedSL m E) :=
    hC.of_le_of_le hCSL le_top
  have hcompOpen : CFSG.Open.IsComponentOf C (StatedSL m E) :=
    (CFSG.Assembly.isComponentOf_iff_open).1 hcomp
  have hsub : (C.subgroupOf (StatedSL m E)).IsSubnormal :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hCSL).1 hcomp.2.1
  have hOpen : CFSG.Open.IsComponentOf (C.subgroupOf (StatedSL m E)) ⊤ := by
    refine ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib hsub, ?_⟩
    exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hCSL) hcompOpen.2.2
  have htop : C.subgroupOf (StatedSL m E) = ⊤ :=
    CFSG.LieType.SemisimpleCentralizers.Held.SLComponentsTrivial_holds m E _ hOpen
  exact le_antisymm hCSL (Subgroup.subgroupOf_eq_top.1 htop)

private theorem map_subgroupOf_eq_statedSL {H : Type} [Group H] {F : Subgroup H} {m : ℕ}
    {E : Type} [Field E] [Finite E] (e : ↥F ≃* GL (Fin m) E) {C0 : Subgroup H}
    (hC0 : IsComponentOf C0 F) :
    (C0.subgroupOf F).map e.toMonoidHom = StatedSL m E := by
  apply eq_statedSL_of_isComponentOf_top
  have hcomp : CFSG.IsComponent (C0.subgroupOf F) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hC0.1).1 hC0
  have hmap : CFSG.IsComponent ((C0.subgroupOf F).map e.toMonoidHom) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponent_map_of_isComponent e hcomp
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_top_iff_native _).2 hmap

public noncomputable def componentEquivStatedSLOfMulEquiv {H : Type} [Group H]
    {F : Subgroup H} {m : ℕ} {E : Type} [Field E] [Finite E]
    (e : ↥F ≃* GL (Fin m) E) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F) :
    ↥C0 ≃* StatedSL m E :=
  (Subgroup.subgroupOfEquivOfLe hC0.1).symm.trans
    ((Subgroup.equivMapOfInjective (C0.subgroupOf F) e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr (map_subgroupOf_eq_statedSL e hC0)))

theorem ggHasLabel_linear_of_supplied
    {C K : Type} [Group C] [Field K] [Finite K] {d n : ℕ} (hd1 : 1 ≤ d)
    (hK : Nat.card K = 2 ^ n)
    (θ : C ⧸ Subgroup.center C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    GGHasLabel (⟨.A, d - 1, n⟩ : LargeEvenLabel) (C ⧸ Subgroup.center C) := by
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  have hd1' : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  refine ⟨?_⟩
  rw [hd1']
  exact θ

public theorem componentEquivStatedSLOfMulEquiv_coe {H : Type} [Group H]
    {F : Subgroup H} {m : ℕ} {E : Type} [Field E] [Finite E]
    (e : ↥F ≃* GL (Fin m) E) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F)
    (x : ↥C0) :
    ((componentEquivStatedSLOfMulEquiv e hC0 x : StatedSL m E) : GL (Fin m) E) =
      e ⟨x, hC0.1 x.2⟩ := by
  simp only [componentEquivStatedSLOfMulEquiv, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply, Subgroup.coe_equivMapOfInjective_apply]
  congr 1

public noncomputable def statedSLQuotEquivLargeEvenProj {m : ℕ} {E : Type} [Field E] :
    StatedSL m E ⧸ Subgroup.center (StatedSL m E) ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin m) E) :=
  (QuotientGroup.congr (Subgroup.center (StatedSL m E))
      (Subgroup.center (LargeEvenSLGroup (Fin m) E))
      (MulEquiv.subgroupCongr
        (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := E) m).symm)
      (Subgroup.map_center_eq (f := MulEquiv.subgroupCongr
        (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := E) m).symm))).trans
    (QuotientGroup.quotientMulEquivOfEq (by
      rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := E) m,
        CFSG.Assembly.largeEvenScalars_eq_statedScalars (ι := Fin m) (K := E)]
      exact CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq m))

public theorem statedSLQuotEquivLargeEvenProj_mk {m : ℕ} {E : Type} [Field E]
    (l : StatedSL m E) :
    statedSLQuotEquivLargeEvenProj (m := m) (E := E) (QuotientGroup.mk l) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin m) E)
        (MulEquiv.subgroupCongr
          (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := E) m).symm l) := by
  rw [statedSLQuotEquivLargeEvenProj, MulEquiv.trans_apply, QuotientGroup.congr_mk,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

public theorem linConjAut_statedSLQuotEquivLargeEvenProj {m : ℕ} {E : Type} [Field E]
    (A : GL (Fin m) E) {l l' : StatedSL m E}
    (h : (l' : GL (Fin m) E) = A * (l : GL (Fin m) E) * A⁻¹) :
    TableB.linConjAut (Fin m) E A
        (statedSLQuotEquivLargeEvenProj (QuotientGroup.mk l)) =
      statedSLQuotEquivLargeEvenProj (QuotientGroup.mk l') := by
  rw [statedSLQuotEquivLargeEvenProj_mk, statedSLQuotEquivLargeEvenProj_mk]
  change TableB.linConjAut (Fin m) E A
      (QuotientGroup.mk (MulEquiv.subgroupCongr
        (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := E) m).symm l)) =
    QuotientGroup.mk (MulEquiv.subgroupCongr
      (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := E) m).symm l')
  rw [TableB.linConjAut_mk]
  apply congrArg (LargeEvenProjMk (LargeEvenSLGroup (Fin m) E))
  apply Subtype.ext
  simpa only [MulAut.conjNormal_apply, MulEquiv.subgroupCongr_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] using h.symm

public noncomputable def linearBlockQuotientMarking {H : Type} [Group H]
    {F : Subgroup H} {m : ℕ} {E : Type} [Field E] [Finite E]
    (e : ↥F ≃* GL (Fin m) E) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F) :
    ↥C0 ⧸ Subgroup.center ↥C0 ≃* LargeEvenProj (LargeEvenSLGroup (Fin m) E) :=
  (QuotientGroup.congr (Subgroup.center ↥C0) (Subgroup.center (StatedSL m E))
      (componentEquivStatedSLOfMulEquiv e hC0)
      (Subgroup.map_center_eq (f := componentEquivStatedSLOfMulEquiv e hC0))).trans
    statedSLQuotEquivLargeEvenProj

public theorem linearBlockQuotientMarking_mk {H : Type} [Group H]
    {F : Subgroup H} {m : ℕ} {E : Type} [Field E] [Finite E]
    (e : ↥F ≃* GL (Fin m) E) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F)
    (x : ↥C0) :
    linearBlockQuotientMarking e hC0 (QuotientGroup.mk x) =
      statedSLQuotEquivLargeEvenProj (QuotientGroup.mk
        (componentEquivStatedSLOfMulEquiv e hC0 x)) := by
  rw [linearBlockQuotientMarking, MulEquiv.trans_apply, QuotientGroup.congr_mk]

public theorem linearBlockQuotientMarking_square {H : Type} [Group H] {F C : Subgroup H}
    {m : ℕ} {E : Type} [Field E] [Finite E]
    (e : ↥F ≃* GL (Fin m) E) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F)
    (ρ : ↥C →* ↥F)
    (hρ : ∀ g : ↥C, ∀ c : ↥F, ((ρ g * c * (ρ g)⁻¹ : ↥F) : H) =
      (g : H) * (c : H) * (g : H)⁻¹)
    (g : ↥C) (c c' : ↥C0)
    (h : (c' : H) = (g : H) * (c : H) * (g : H)⁻¹) :
    TableB.linConjAut (Fin m) E (e (ρ g))
        (linearBlockQuotientMarking e hC0 (QuotientGroup.mk c)) =
      linearBlockQuotientMarking e hC0 (QuotientGroup.mk c') := by
  rw [linearBlockQuotientMarking_mk, linearBlockQuotientMarking_mk]
  apply linConjAut_statedSLQuotEquivLargeEvenProj
  rw [componentEquivStatedSLOfMulEquiv_coe, componentEquivStatedSLOfMulEquiv_coe]
  have hcF : (⟨c', hC0.1 c'.2⟩ : ↥F) =
      ρ g * (⟨c, hC0.1 c.2⟩ : ↥F) * (ρ g)⁻¹ := by
    apply Subtype.ext
    exact h.trans (hρ g ⟨c, hC0.1 c.2⟩).symm
  rw [hcF, map_mul, map_mul, map_inv]

private noncomputable def statedSLCenterQuotEquivProjective {m : ℕ} {E : Type} [Field E] :
    StatedSL m E ⧸ Subgroup.center (StatedSL m E) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL m E :=
  (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq m)).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center m E)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)).symm

private theorem statedSLCenterQuotEquivProjective_mk {m : ℕ} {E : Type} [Field E]
    (l : StatedSL m E) :
    statedSLCenterQuotEquivProjective (m := m) (E := E) (QuotientGroup.mk l) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m E
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l) := by
  rw [statedSLCenterQuotEquivProjective]
  simp only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem recipeEquiv_statedSLQuotEquivLargeEvenProj_mk {m : ℕ} {E : Type} [Field E]
    (l : StatedSL m E) :
    TypeA.recipeEquiv m E
        (statedSLQuotEquivLargeEvenProj (m := m) (E := E) (QuotientGroup.mk l)) =
      statedSLCenterQuotEquivProjective (m := m) (E := E) (QuotientGroup.mk l) := by
  rw [statedSLCenterQuotEquivProjective_mk, statedSLQuotEquivLargeEvenProj_mk,
    TypeA.recipeEquiv_mk]
  congr 1
  apply Subtype.ext
  have h1 : ((TypeA.slKerEquiv m E ((MulEquiv.subgroupCongr
      (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := E) m).symm) l) :
      Matrix.SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) =
      ((l : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) := by
    rw [TypeA.coe_slKerEquiv]
    rfl
  have h2 : (((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l :
      Matrix.SpecialLinearGroup (Fin m) E) : Matrix (Fin m) (Fin m) E) =
      ((l : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) := by
    have h := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  exact h1.trans h2.symm

private theorem specialLinearGroupEquivStatedSL_symm_slConjugation {m : ℕ} {E : Type} [Field E]
    {A : GL (Fin m) E} {l l' : StatedSL m E}
    (h : (l' : GL (Fin m) E) = A * (l : GL (Fin m) E) * A⁻¹) :
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l' =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l) := by
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  apply Units.ext
  have hl : (l : GL (Fin m) E) =
      ((e.symm l : Matrix.SpecialLinearGroup (Fin m) E) : GL (Fin m) E) := by
    conv_lhs => rw [← MulEquiv.apply_symm_apply e l]
    exact Units.ext (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E (e.symm l))
  have h' := congrArg (fun u : GL (Fin m) E => (u : Matrix (Fin m) (Fin m) E)) h
  rw [hl] at h'
  rw [show ((e (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
        (e.symm l)) : StatedSL m E) : GL (Fin m) E) =
      Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
          (e.symm l)) from
    Units.ext (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E _)]
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  exact h'

private theorem specialLinearGroupEquivStatedSL_symm_slSemilinear {m : ℕ} {E : Type} [Field E]
    {B : GL (Fin m) E} {τ : E ≃+* E} {l l' : StatedSL m E}
    (h : (l' : GL (Fin m) E) =
      B * Matrix.GeneralLinearGroup.map τ.toRingHom (l : GL (Fin m) E) * B⁻¹) :
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l' =
      CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction m E B τ
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l) := by
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E
  apply e.injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  have hl : (l : GL (Fin m) E) =
      Matrix.SpecialLinearGroup.toGL (e.symm l) := by
    conv_lhs => rw [← MulEquiv.apply_symm_apply e l]
    exact Units.ext (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E (e.symm l))
  have hl' : (l' : GL (Fin m) E) =
      Matrix.SpecialLinearGroup.toGL (e.symm l') := by
    conv_lhs => rw [← MulEquiv.apply_symm_apply e l']
    exact Units.ext (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E (e.symm l'))
  rw [show ((e (CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction m E B τ
        (e.symm l)) : StatedSL m E) : GL (Fin m) E) =
      Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction m E B τ
          (e.symm l)) from
    Units.ext (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe m E _)]
  rw [CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction_toGL]
  rw [hl']
  rw [hl', hl] at h
  change Matrix.SpecialLinearGroup.toGL (e.symm l') =
    B * Matrix.GeneralLinearGroup.map τ.toRingHom
      (Matrix.SpecialLinearGroup.toGL (e.symm l)) * B⁻¹
  exact h

private theorem proj_slSemilinear {m : ℕ} {E : Type} [Field E]
    (B : GL (Fin m) E) (τ : E ≃+* E) (g : Matrix.SpecialLinearGroup (Fin m) E) :
    LinearFlag.proj m E
        (CFSG.ComponentClassification.CatalogueBLinearSemilinear.slSemilinearAction m E B τ g) =
      (LinearFlag.conjAut m E B * LinearFlag.fieldAut m E τ)
        (LinearFlag.proj m E g) := by
  rw [MulAut.mul_apply, LinearFlag.fieldAut_proj, LinearFlag.conjAut_proj]
  rfl

public theorem linearBlockQuotientMarking_semilinear {H : Type} [Group H]
    {F : Subgroup H} {m : ℕ} {E : Type} [Field E] [Finite E]
    (e : ↥F ≃* GL (Fin m) E) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F)
    (f' : MulAut ↥C0) (B : GL (Fin m) E) (τ : E ≃+* E)
    (hsq : ∀ c : ↥C0,
      (e ⟨f' c, hC0.1 (f' c).2⟩ : GL (Fin m) E) =
        B * Matrix.GeneralLinearGroup.map τ.toRingHom (e ⟨c, hC0.1 c.2⟩) * B⁻¹)
    (x : ↥C0) :
    TypeA.recipeEquiv m E
        (linearBlockQuotientMarking e hC0 (QuotientGroup.mk (f' x))) =
      LinearFlag.conjAut m E B
        (LinearFlag.fieldAut m E τ
          (TypeA.recipeEquiv m E
            (linearBlockQuotientMarking e hC0 (QuotientGroup.mk x)))) := by
  let ec := componentEquivStatedSLOfMulEquiv e hC0
  let l : StatedSL m E := ec (f' x)
  let l0 : StatedSL m E := ec x
  have hsq' : (l : GL (Fin m) E) =
      B * Matrix.GeneralLinearGroup.map τ.toRingHom (l0 : GL (Fin m) E) * B⁻¹ := by
    rw [show (l : GL (Fin m) E) =
        (e ⟨f' x, hC0.1 (f' x).2⟩ : GL (Fin m) E) from
      componentEquivStatedSLOfMulEquiv_coe e hC0 (f' x)]
    rw [show (l0 : GL (Fin m) E) =
        (e ⟨x, hC0.1 x.2⟩ : GL (Fin m) E) from
      componentEquivStatedSLOfMulEquiv_coe e hC0 x]
    exact hsq x
  have hSL := specialLinearGroupEquivStatedSL_symm_slSemilinear (m := m) (E := E)
    (B := B) (τ := τ) (l := l0) (l' := l) hsq'
  rw [linearBlockQuotientMarking_mk, linearBlockQuotientMarking_mk]
  rw [recipeEquiv_statedSLQuotEquivLargeEvenProj_mk,
    recipeEquiv_statedSLQuotEquivLargeEvenProj_mk]
  rw [statedSLCenterQuotEquivProjective_mk, statedSLCenterQuotEquivProjective_mk]
  rw [hSL, proj_slSemilinear]
  rfl

public theorem not_largeEvenInduces_of_semilinear_linearBlock {H : Type} [Group H]
    {F : Subgroup H} {m : ℕ} {E : Type} [Field E] [Finite E]
    (e : ↥F ≃* GL (Fin m) E) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F)
    (hm : 2 ≤ m) (f' : MulAut ↥C0) (B : GL (Fin m) E) (τ : E ≃+* E) (hτ : τ ≠ 1)
    (hsq : ∀ c : ↥C0,
      (e ⟨f' c, hC0.1 (f' c).2⟩ : GL (Fin m) E) =
        B * Matrix.GeneralLinearGroup.map τ.toRingHom (e ⟨c, hC0.1 c.2⟩) * B⁻¹)
    {I : Set (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin m) E)))}
    (hI : I = LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin m) E)) Set.univ) :
    ¬ ∃ φ ∈ Subgroup.closure I,
      LargeEvenInduces (linearBlockQuotientMarking e hC0)
        (fun c c' : ↥C0 => f' c = c') φ := by
  classical
  rintro ⟨φ, hφcl, hφ⟩
  have hIrec : I = (RecipeFieldLinear.recI m E : Set _) := by
    rw [hI, ← RecipeFieldLinear.coe_recI]
  have hφI : φ ∈ RecipeFieldLinear.recI m E := by
    rw [hIrec] at hφcl
    rwa [Subgroup.closure_eq] at hφcl
  obtain ⟨A, hA⟩ := LinearFlag.mem_linearAutGroup_iff.1
    (RecipeFieldLinear.mem_recI_iff.1 hφI)
  let θ := linearBlockQuotientMarking e hC0
  let ρ := TypeA.recipeEquiv m E
  have hsurj : Function.Surjective (fun c : ↥C0 => ρ (θ (QuotientGroup.mk c))) :=
    ρ.surjective.comp (θ.surjective.comp (QuotientGroup.mk_surjective (s := Subgroup.center ↥C0)))
  have hpoint : ∀ c : ↥C0,
      LinearFlag.conjAut m E A (ρ (θ (QuotientGroup.mk c))) =
        LinearFlag.conjAut m E B (LinearFlag.fieldAut m E τ
          (ρ (θ (QuotientGroup.mk c)))) := by
    intro c
    have h := hφ c (f' c) rfl
    have h' := congrArg ρ h
    have hAcongr : LinearFlag.conjAut m E A (ρ (θ (QuotientGroup.mk c))) =
        ρ (φ (θ (QuotientGroup.mk c))) := by
      have hAc := congrArg
        (fun f : MulAut (LinearFlag.projectiveSL m E) => f (ρ (θ (QuotientGroup.mk c)))) hA
      change LinearFlag.conjAut m E A (ρ (θ (QuotientGroup.mk c))) =
        ρ (φ (ρ.symm (ρ (θ (QuotientGroup.mk c))))) at hAc
      rwa [MulEquiv.symm_apply_apply] at hAc
    have hact := linearBlockQuotientMarking_semilinear e hC0 f' B τ hsq c
    calc LinearFlag.conjAut m E A (ρ (θ (QuotientGroup.mk c)))
        = ρ (φ (θ (QuotientGroup.mk c))) := hAcongr
      _ = ρ (θ (QuotientGroup.mk (f' c))) := h'
      _ = LinearFlag.conjAut m E B (LinearFlag.fieldAut m E τ
            (ρ (θ (QuotientGroup.mk c)))) := hact
  have hforall : ∀ y : LinearFlag.projectiveSL m E,
      LinearFlag.conjAut m E A y =
        LinearFlag.conjAut m E B (LinearFlag.fieldAut m E τ y) := by
    intro y
    obtain ⟨c, rfl⟩ := hsurj y
    exact hpoint c
  have hcomp : LinearFlag.conjAut m E A =
      LinearFlag.conjAut m E B * LinearFlag.fieldAut m E τ := by
    ext y
    simpa using hforall y
  refine fniLin_not_inner hm hτ B A (fun y => ?_)
  have := congrArg (fun f : MulAut (LinearFlag.projectiveSL m E) => f y) hcomp
  simpa using this.symm

private theorem largeEvenRawDatumLegacy_linear {m f : ℕ} {E : Type} [Field E] [Finite E]
    (hm : 1 ≤ m) (hcard : Nat.card E = 2 ^ f) (Q : LargeEvenRawCont)
    (hQ : Q (LargeEvenProj (LargeEvenSLGroup (Fin m) E))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin m) E)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin m) E)))) :
    LargeEvenRawDatumLegacy (⟨.A, m - 1, f⟩ : LargeEvenLabel) Q := by
  change LargeEvenRecipeLinear (m - 1 + 1) (2 ^ f) Q
  rw [show m - 1 + 1 = m from Nat.sub_add_cancel (by omega)]
  exact ⟨E, inferInstance, inferInstance, hcard, hQ⟩

private theorem largeEvenInLambda2_linearLabel {m f : ℕ} (hm : 2 ≤ m) (hf : 1 ≤ f)
    (hmf : m = 2 → 2 ≤ f) :
    LargeEvenInLambda2 (⟨.A, m - 1, f⟩ : LargeEvenLabel) := by
  refine ⟨hf, by show 1 ≤ m - 1; omega, ?_⟩
  intro h
  have h' : m - 1 = 1 := by simpa using h
  exact hmf (by omega)

private theorem largeEvenMarking_statedSL_linear {m f : ℕ} {E : Type} [Field E] [Finite E]
    (hcard : Nat.card E = 2 ^ f)
    (hperf : commutator (StatedSL m E) = ⊤)
    (hsimp : IsSimpleGroup (StatedSL m E ⧸ Subgroup.center (StatedSL m E)))
    (hm : 2 ≤ m) (hf : 1 ≤ f) (hmf : m = 2 → 2 ≤ f) :
    LargeEvenMarking (StatedSL m E)
      (fun lab _ _ I _ θ => GGChevStTag lab ∧
        ∀ ε ∈ (⊤ : Subgroup (GL (Fin m) E)), ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : GL (Fin m) E) = ε⁻¹ * l * ε) φ) := by
  refine ⟨hperf, ⟨⟨.A, m - 1, f⟩, largeEvenInLambda2_linearLabel hm hf hmf, ?_⟩⟩
  · refine largeEvenRawDatumLegacy_linear (by omega) hcard _ ?_
    let θ : StatedSL m E ⧸ Subgroup.center (StatedSL m E) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin m) E) :=
      statedSLCenterQuotEquivProjective.trans
        (CFSG.StandardType.TypeA.recipeEquiv m E).symm
    have hnab : ∃ a b : StatedSL m E ⧸ Subgroup.center (StatedSL m E), a * b ≠ b * a :=
      exists_mul_ne_mul_centerQuot_of_perfect hperf inferInstance
    refine ⟨?_, ?_, θ, by simp [GGChevStTag], ?_⟩
    · exact θ.symm.isSimpleGroup_congr.mpr hsimp
    · exact nonabelian_of_mulEquiv θ hnab
    · intro ε _
      let A : GL (Fin m) E := ε⁻¹
      let φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin m) E)) :=
        (MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv m E)).symm
          (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut m E A)
      refine ⟨φ, CFSG.StandardType.NbrGraphLinear.symm_congr_conjAut_mem A, ?_⟩
      intro l l' hll'
      apply (CFSG.StandardType.TypeA.recipeEquiv m E).injective
      simp only [φ, MulAut.congr_symm_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
      rw [show CFSG.StandardType.TypeA.recipeEquiv m E
            (θ (QuotientGroup.mk l)) =
          statedSLCenterQuotEquivProjective (QuotientGroup.mk l) from rfl,
        show CFSG.StandardType.TypeA.recipeEquiv m E
            (θ (QuotientGroup.mk l')) =
          statedSLCenterQuotEquivProjective (QuotientGroup.mk l') from rfl]
      rw [statedSLCenterQuotEquivProjective_mk, statedSLCenterQuotEquivProjective_mk]
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
      rw [← specialLinearGroupEquivStatedSL_symm_slConjugation (A := A)
        (by simpa [A] using hll')]

private theorem two_le_of_isSimpleGroup_centerQuot_statedSL {m : ℕ} {E : Type} [Field E]
    [Finite E]
    (hsimp : IsSimpleGroup (StatedSL m E ⧸ Subgroup.center (StatedSL m E))) : 2 ≤ m := by
  by_contra h
  have hm1 : m ≤ 1 := by omega
  have hsub : Subsingleton (StatedSL m E) :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_subsingleton_statedSL_of_le_one hm1
  have hntq : Nontrivial (StatedSL m E ⧸ Subgroup.center (StatedSL m E)) :=
    hsimp.toNontrivial
  have hsubq : Subsingleton (StatedSL m E ⧸ Subgroup.center (StatedSL m E)) := by
    constructor
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [QuotientGroup.eq]
        have h1 : a⁻¹ * b = 1 := hsub.elim _ _
        rw [h1]
        exact (Subgroup.center (StatedSL m E)).one_mem
  obtain ⟨a, b, hab⟩ := hntq
  exact hab (hsubq.elim a b)

private theorem two_le_of_card_two_statedSL {f : ℕ} {E : Type} [Field E] [Finite E]
    (hf : 1 ≤ f) (hcard : Nat.card E = 2 ^ f)
    (hperf : commutator (StatedSL 2 E) = ⊤)
    (hsimp : IsSimpleGroup (StatedSL 2 E ⧸ Subgroup.center (StatedSL 2 E))) : 2 ≤ f := by
  by_contra hf2
  have hf1 : f = 1 := by omega
  have hcard2 : Nat.card E = 2 := by rw [hcard, hf1, pow_one]
  have hcardSL : Nat.card (StatedSL 2 E) = 6 := by
    rw [CFSG.Open.StatedAPI.card_statedSL_two, hcard2]
    norm_num
  have hsolv : Group.IsSolvable (StatedSL 2 E) := by
    have hcard6 : @Fintype.card (StatedSL 2 E) (Fintype.ofFinite _) = 2 ^ 1 * 3 ^ 1 := by
      rw [← @Nat.card_eq_fintype_card (StatedSL 2 E) (Fintype.ofFinite _), hcardSL]
      norm_num
    exact @CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (StatedSL 2 E) _ (Fintype.ofFinite _) 2 3 1 1 Nat.prime_two Nat.prime_three
      (by norm_num) hcard6
  have hntq : Nontrivial (StatedSL 2 E ⧸ Subgroup.center (StatedSL 2 E)) :=
    hsimp.toNontrivial
  have hnt : Nontrivial (StatedSL 2 E) :=
    @Function.Surjective.nontrivial (StatedSL 2 E)
      (StatedSL 2 E ⧸ Subgroup.center (StatedSL 2 E)) hntq (QuotientGroup.mk)
      (QuotientGroup.mk_surjective (s := Subgroup.center (StatedSL 2 E)))
  have hperf' : Group.IsPerfect (StatedSL 2 E) := Group.isPerfect_def.mpr hperf
  exact @Group.IsPerfect.not_isSolvable (StatedSL 2 E) _ hnt hperf' hsolv

private theorem componentEquivStatedSL_isSimpleQuot {H : Type} [Group H] {F : Subgroup H}
    {m : ℕ} {E : Type} [Field E] [Finite E]
    (e : ↥F ≃* GL (Fin m) E) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F) :
    IsSimpleGroup (StatedSL m E ⧸ Subgroup.center (StatedSL m E)) := by
  let ec := componentEquivStatedSLOfMulEquiv e hC0
  exact (QuotientGroup.congr (Subgroup.center ↥C0) (Subgroup.center (StatedSL m E)) ec
    (Subgroup.map_center_eq (f := ec))).isSimpleGroup_congr.mp hC0.2.2.2

private theorem componentEquivStatedSL_commutator {H : Type} [Group H] {F : Subgroup H}
    {m : ℕ} {E : Type} [Field E] [Finite E]
    (e : ↥F ≃* GL (Fin m) E) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F) :
    commutator (StatedSL m E) = ⊤ := by
  let ec := componentEquivStatedSLOfMulEquiv e hC0
  haveI : Group.IsPerfect ↥C0 := Group.isPerfect_def.mpr hC0.2.2.1
  exact (Group.IsPerfect.ofSurjective (f := ec.toMonoidHom) ec.surjective).commutator_eq_top

public theorem largeEvenMarking_linearBlock_of_semilinear {H : Type} [Group H]
    {F : Subgroup H} {m : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (e : ↥F ≃* GL (Fin m) E) {C0 : Subgroup H} (hC0 : IsComponentOf C0 F)
    (f' : MulAut ↥C0) (B : GL (Fin m) E) (τ : E ≃+* E) (hτ : τ ≠ 1)
    (hsq : ∀ c : ↥C0,
      (e ⟨f' c, hC0.1 (f' c).2⟩ : GL (Fin m) E) =
        B * Matrix.GeneralLinearGroup.map τ.toRingHom (e ⟨c, hC0.1 c.2⟩) * B⁻¹) :
    LargeEvenMarking ↥C0
      (fun _ _ _ I _ θ =>
        ¬ ∃ φ ∈ Subgroup.closure I,
          LargeEvenInduces θ (fun c c' : ↥C0 => f' c = c') φ) := by
  obtain ⟨n, -, hfcard⟩ := @FiniteField.card E _ (Fintype.ofFinite E) 2 _
  let f : ℕ := n
  have hcard : Nat.card E = 2 ^ f := by
    rw [@Nat.card_eq_fintype_card E (Fintype.ofFinite E), hfcard]
  have hperf : commutator (StatedSL m E) = ⊤ :=
    componentEquivStatedSL_commutator e hC0
  have hsimp : IsSimpleGroup (StatedSL m E ⧸ Subgroup.center (StatedSL m E)) :=
    componentEquivStatedSL_isSimpleQuot e hC0
  have hm : 2 ≤ m := two_le_of_isSimpleGroup_centerQuot_statedSL hsimp
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · rw [h0, pow_zero] at hcard
      have := Finite.one_lt_card (α := E)
      omega
    · exact h
  have hmf : m = 2 → 2 ≤ f := by
    intro hm2
    subst m
    exact two_le_of_card_two_statedSL hf hcard hperf hsimp
  refine ⟨hC0.2.2.1, ⟨⟨.A, m - 1, f⟩,
    largeEvenInLambda2_linearLabel hm hf hmf, ?_⟩⟩
  refine largeEvenRawDatumLegacy_linear (by omega) hcard _ ?_
  refine ⟨?_, ?_, linearBlockQuotientMarking e hC0, ?_⟩
  · exact statedSLQuotEquivLargeEvenProj.isSimpleGroup_congr.mp hsimp
  · exact nonabelian_of_mulEquiv statedSLQuotEquivLargeEvenProj
      (exists_mul_ne_mul_centerQuot_of_perfect hperf inferInstance)
  · exact not_largeEvenInduces_of_semilinear_linearBlock e hC0 hm f' B τ hτ hsq rfl

theorem exists_linear_label_of_isComponentOf_iso_generalLinear
    {H : Type} [Group H] {F : Subgroup H} {m : ℕ} {E : Type}
    [Field E] [Finite E] [CharP E 2] (e : ↥F ≃* GL (Fin m) E)
    {C : Subgroup H} (hC : IsComponentOf C F) :
    ∃ f : ℕ, 1 ≤ f ∧ Nat.card E = 2 ^ f ∧
      LargeEvenInLambda2 (⟨.A, m - 1, f⟩ : LargeEvenLabel) ∧
      GGHasLabel ⟨.A, m - 1, f⟩ (↥C ⧸ Subgroup.center ↥C) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, -, hcardF⟩ := @FiniteField.card E _ (Fintype.ofFinite E) 2 _
  let f : ℕ := n
  have hcard : Nat.card E = 2 ^ f := by
    rw [@Nat.card_eq_fintype_card E (Fintype.ofFinite E), hcardF]
  have hf : 1 ≤ f := by
    by_contra h
    have hf0 : f = 0 := by omega
    have hE := Finite.one_lt_card (α := E)
    rw [hcard, hf0, pow_zero] at hE
    omega
  have hsimp := componentEquivStatedSL_isSimpleQuot e hC
  have hperf := componentEquivStatedSL_commutator e hC
  have hm := two_le_of_isSimpleGroup_centerQuot_statedSL hsimp
  have hmf : m = 2 → 2 ≤ f := by
    intro hm2
    subst m
    exact two_le_of_card_two_statedSL hf hcard hperf hsimp
  let ec := componentEquivStatedSLOfMulEquiv e hC
  let θ : ↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin m) E) :=
    (QuotientGroup.congr _ _ ec (Subgroup.map_center_eq (f := ec))).trans
      statedSLQuotEquivLargeEvenProj
  exact ⟨f, hf, hcard, largeEvenInLambda2_linearLabel hm hf hmf,
    ggHasLabel_linear_of_supplied (by omega) hcard θ⟩

theorem ggE0Concl_top_statedSL {m : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2] :
    GGE0Concl (⊤ : Subgroup (GL (Fin m) E)) (StatedSL m E) := by
  obtain ⟨n, -, hfcard⟩ := @FiniteField.card E _ (Fintype.ofFinite E) 2 _
  let f : ℕ := n
  have hcard : Nat.card E = 2 ^ f := by
    rw [@Nat.card_eq_fintype_card E (Fintype.ofFinite E), hfcard]
  have hnorm : (StatedSL m E).Normal := by
    rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]
    infer_instance
  refine ⟨?_, fun hmark => ?_⟩
  · rw [@Subgroup.normalizer_eq_top (GL (Fin m) E) _ (StatedSL m E) hnorm]
  have hperf : commutator (StatedSL m E) = ⊤ := hmark.1
  obtain ⟨lab, hlab, hrawLeg⟩ := hmark.2
  have hraw : LargeEvenRawDatum lab _ := (largeEvenRawDatum_legacy lab _).2 hrawLeg
  obtain ⟨R, _, I, F, hsimple, hnonab, θ, -⟩ := largeEvenRawDatum_exists hraw
  have hsimp : IsSimpleGroup (StatedSL m E ⧸ Subgroup.center (StatedSL m E)) :=
    θ.isSimpleGroup_congr.mpr hsimple
  have hm : 2 ≤ m := two_le_of_isSimpleGroup_centerQuot_statedSL hsimp
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · rw [h0, pow_zero] at hcard
      have := Finite.one_lt_card (α := E)
      omega
    · exact h
  have hmf : m = 2 → 2 ≤ f := by
    intro hm2
    subst m
    exact two_le_of_card_two_statedSL hf hcard hperf hsimp
  exact largeEvenMarking_statedSL_linear hcard hperf hsimp hm hf hmf

theorem largeEvenMarking_of_isComponentOf_top_generalLinear {m : ℕ} {E : Type} [Field E]
    [Finite E] [CharP E 2] {C : Subgroup (GL (Fin m) E)} (hC : IsComponentOf C ⊤) :
    LargeEvenMarking C (fun _ _ _ _ _ _ => True) := by
  obtain rfl := eq_statedSL_of_isComponentOf_top hC
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨n, -, hfcard⟩ := @FiniteField.card E _ (Fintype.ofFinite E) 2 ‹CharP E 2›
  let f : ℕ := n
  have hcard : Nat.card E = 2 ^ f := by
    rw [Nat.card_eq_fintype_card, hfcard]
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h
    · rw [h0, pow_zero] at hcard
      have := Finite.one_lt_card (α := E)
      omega
    · exact h
  have hm : 2 ≤ m := two_le_of_isSimpleGroup_centerQuot_statedSL hC.2.2.2
  have hmf : m = 2 → 2 ≤ f := by
    rintro rfl
    exact two_le_of_card_two_statedSL hf hcard hC.2.2.1 hC.2.2.2
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
    (largeEvenMarking_statedSL_linear hcard hC.2.2.1 hC.2.2.2 hm hf hmf)

theorem ggE0Concl_top_generalLinear {m : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (C : Subgroup (GL (Fin m) E)) (hC : IsComponentOf C ⊤) : GGE0Concl ⊤ C := by
  rw [eq_statedSL_of_isComponentOf_top hC]
  exact ggE0Concl_top_statedSL

end CFSG.StandardType
