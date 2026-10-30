module

public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagModel
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpDecomp
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet

import CFSG.LocalAnalysis.StandardType.GGTableBLinear
import CFSG.Assembly.GL83StatedBridge
import CFSG.ClassicalInvolution.Phan.CenterScalars
import CFSG.ClassicalGroups.Unitary.Finite
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2BlockProj
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.GroupTheory.IsComponentOfMap
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GSympLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GCenterQuot
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniLabelPSU
import CFSG.ClassicalInvolution.Q3.TA3LeafQ5U3Frame
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.Open (StatedSL StatedSp StatedSU StatedScalars StatedProj)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.GLTheoremA.Y10GSympLabel CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot
open CFSG.StandardType.ClassicalBlocks CFSG.StandardType.ClassicalPosition

private noncomputable def l02qq2spb_statedSLCenterQuotEquivProjective {m : ℕ} {E : Type} [Field E] :
    StatedSL m E ⧸ Subgroup.center (StatedSL m E) ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL m E :=
  (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.SemisimpleCentralizers.Held.center_statedSL_eq m)).trans
    ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center m E)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj m E)).symm

private theorem l02qq2spb_statedSLCenterQuotEquivProjective_mk {m : ℕ} {E : Type} [Field E]
    (l : StatedSL m E) :
    l02qq2spb_statedSLCenterQuotEquivProjective (m := m) (E := E) (QuotientGroup.mk l) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m E
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm l) := by
  rw [l02qq2spb_statedSLCenterQuotEquivProjective]
  simp only [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

private theorem l02qq2spb_specialLinearGroupEquivStatedSL_symm_slConjugation {m : ℕ} {E : Type}
    [Field E] {A : GL (Fin m) E} {l l' : StatedSL m E}
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

private theorem l02qq2spb_projMk_eq_iff {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) (x y : ↥H) :
    LargeEvenProjMk H x = LargeEvenProjMk H y ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c = (x : GL ι K)⁻¹ * (y : GL ι K) := by
  rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_range

private theorem l02qq2spb_ker_projMk_le_center {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (H : Subgroup (GL ι K)) : (LargeEvenProjMk H).ker ≤ Subgroup.center ↥H := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hx' : LargeEvenProjMk H x = LargeEvenProjMk H 1 := by rw [hx, map_one]
  obtain ⟨c, hc⟩ := (l02qq2spb_projMk_eq_iff H x 1).mp hx'
  have hxG : (x : GL ι K) = Matrix.GeneralLinearGroup.scalar ι c⁻¹ := by
    have : (x : GL ι K)⁻¹ = Matrix.GeneralLinearGroup.scalar ι c := by simpa using hc.symm
    rw [map_inv, ← this, inv_inv]
  have hxZ : (x : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c⁻¹, hxG.symm⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact Subgroup.mem_center_iff.1 hxZ (y : GL ι K)

private theorem l02qq2spb_slKerEquiv_conjNormal {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (z : ↥(LargeEvenSLGroup (Fin d) K)) :
    CFSG.StandardType.TypeA.slKerEquiv d K
        (MulAut.conjNormal (H := LargeEvenSLGroup (Fin d) K) A z) =
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation d K A
        (CFSG.StandardType.TypeA.slKerEquiv d K z) := by
  apply Subtype.ext
  rw [CFSG.StandardType.TypeA.coe_slKerEquiv,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix,
    CFSG.StandardType.TypeA.coe_slKerEquiv]
  rw [MulAut.conjNormal_apply]
  rfl

private theorem l02qq2spb_recipeEquiv_linConjAut {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (z : LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    CFSG.StandardType.TypeA.recipeEquiv d K (TableB.linConjAut (Fin d) K A z) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d K A
        (CFSG.StandardType.TypeA.recipeEquiv d K z) := by
  induction z using QuotientGroup.induction_on with
  | H h =>
    rw [TableB.linConjAut_mk]
    change CFSG.StandardType.TypeA.recipeEquiv d K
        (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)
          (MulAut.conjNormal (H := LargeEvenSLGroup (Fin d) K) A h)) =
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d K A
        (CFSG.StandardType.TypeA.recipeEquiv d K
          (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K) h))
    rw [CFSG.StandardType.TypeA.recipeEquiv_mk, CFSG.StandardType.TypeA.recipeEquiv_mk,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj,
      l02qq2spb_slKerEquiv_conjNormal]

private theorem l02qq2spb_recipeEquiv_symm_linConjAut {d : ℕ} {K : Type} [Field K]
    (A : GL (Fin d) K) (z : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL d K) :
    TableB.linConjAut (Fin d) K A ((CFSG.StandardType.TypeA.recipeEquiv d K).symm z) =
      (CFSG.StandardType.TypeA.recipeEquiv d K).symm
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut d K A z) := by
  apply (CFSG.StandardType.TypeA.recipeEquiv d K).injective
  have h := l02qq2spb_recipeEquiv_linConjAut (d := d) (K := K) A
    ((CFSG.StandardType.TypeA.recipeEquiv d K).symm z)
  rw [h, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

private theorem l02qq2spb_not_iso_twA_A {r n d k : ℕ} :
    ¬ GGLabelIso (⟨.twA, r, n⟩ : LargeEvenLabel) ⟨.A, d, k⟩ := by
  rintro (h | h | h | h | h | h | h | h)
  · exact (by cases h)
  · rcases h.1 with h' | h' <;> exact (by cases h')
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.2)
  · exact (by cases h.1)
  · exact (by cases h.2)

private theorem l02qq2spb_not_iso_B_A {r n d k : ℕ} :
    ¬ GGLabelIso (⟨.B, r, n⟩ : LargeEvenLabel) ⟨.A, d, k⟩ := by
  rintro (h | h | h | h | h | h | h | h)
  · exact (by cases h)
  · rcases h.2.1 with h' | h' <;> exact (by cases h')
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)

private theorem l02qq2spb_not_iso_A1_Ad {f d k : ℕ} (hd : 3 ≤ d) :
    ¬ GGLabelIso (⟨.A, 1, f⟩ : LargeEvenLabel) ⟨.A, d - 1, k⟩ := by
  rintro (h | h | h | h | h | h | h | h)
  · have h1 : 1 = d - 1 := by simpa using congrArg LargeEvenLabel.rank h
    omega
  · rcases h.2.1 with h' | h' <;> exact (by cases h')
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)

private theorem l02qq2spb_not_iso_B2der_A {d k : ℕ} (hd : 3 ≤ d) :
    ¬ GGLabelIso (⟨.B2der, 0, 1⟩ : LargeEvenLabel) ⟨.A, d - 1, k⟩ := by
  rintro (h | h | h | h | h | h | h | h)
  · exact (by cases h)
  · rcases h.2.1 with h' | h' <;> exact (by cases h')
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)
  · exact (by cases h.1)

theorem l02qq2spb_symp_excl {G : Type} [Group G] {d n₁ : ℕ} (hd : 3 ≤ d)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
    {C Blk : Subgroup G}
    (hCε : CFSG.Assembly.IsComponentOf C Blk)
    (eS : ↥Blk ≃* ↥(StatedSp n₁ K))
    (θC : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K')) :
    False := by
  obtain ⟨f₀, -, hKf0⟩ := @FiniteField.card K _ (Fintype.ofFinite K) 2 (by infer_instance)
  obtain ⟨f, hf1, hKf⟩ : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f :=
    ⟨f₀, f₀.pos, by rw [@Nat.card_eq_fintype_card K (Fintype.ofFinite K), hKf0]⟩
  obtain ⟨k₀, -, hK'0⟩ := @FiniteField.card K' _ (Fintype.ofFinite K') 2 (by infer_instance)
  obtain ⟨k', hk'1, hK'⟩ : ∃ k' : ℕ, 1 ≤ k' ∧ Nat.card K' = 2 ^ k' :=
    ⟨k₀, k₀.pos, by rw [@Nat.card_eq_fintype_card K' (Fintype.ofFinite K'), hK'0]⟩
  have hθC : GGHasLabel (⟨.A, d - 1, k'⟩ : LargeEvenLabel)
      (↥C ⧸ Subgroup.center ↥C) := by
    unfold GGHasLabel
    rw [show LargeEvenRawDatum (⟨.A, d - 1, k'⟩ : LargeEvenLabel) _ =
        LargeEvenRecipeLinear ((d - 1) + 1) (2 ^ k') _ from rfl]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
    exact ⟨K', inferInstance, inferInstance, hK', ⟨θC⟩⟩
  have hA_lambda : LargeEvenInLambda2 (⟨.A, d - 1, k'⟩ : LargeEvenLabel) :=
    ⟨hk'1, by show 1 ≤ d - 1; omega, fun h => by change d - 1 = 1 at h; omega⟩
  let Cb : Subgroup ↥Blk := C.subgroupOf Blk
  have hCb : CFSG.Assembly.IsComponentOf Cb (⊤ : Subgroup ↥Blk) := by
    refine (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := Blk.subtype) (Subgroup.subtype_injective _)).mp ?_
    have hmapCb : Subgroup.map Blk.subtype Cb = C := Subgroup.map_subgroupOf_eq_of_le hCε.1
    simpa only [hmapCb, Subgroup.map_top, Subgroup.range_subtype] using hCε
  have hCbmap_component : CFSG.Assembly.IsComponentOf (Cb.map eS.toMonoidHom)
      (⊤ : Subgroup ↥(StatedSp n₁ K)) := by
    have htop : (⊤ : Subgroup ↥Blk).map eS.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top]; exact eS.surjective
    have h := isComponentOf_map_mulEquiv eS ((CFSG.Assembly.isComponentOf_iff_open).1 hCb)
    rw [htop] at h
    exact (CFSG.Assembly.isComponentOf_iff_open).2 h
  have hcompGL : CFSG.Assembly.IsComponentOf
      ((Cb.map eS.toMonoidHom).map (StatedSp n₁ K).subtype) (StatedSp n₁ K) := by
    have := (isComponentOf_map_iff (f := (StatedSp n₁ K).subtype)
      (Subgroup.subtype_injective _)).mpr hCbmap_component
    simpa only [Subgroup.map_top, Subgroup.range_subtype] using this
  by_cases h0 : n₁ = 0
  · exact (not_isComponentOf_statedSp_of_small (Or.inl h0) _) hcompGL
  by_cases h1s : n₁ = 1 ∧ Nat.card K = 2
  · exact (not_isComponentOf_statedSp_of_small (Or.inr h1s) _) hcompGL
  by_cases h42 : n₁ = 2 ∧ Nat.card K = 2
  · obtain ⟨h42n, h42K⟩ := h42
    subst h42n
    have hspbot : Subgroup.center ↥(StatedSp 2 K) = ⊥ :=
      CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (F := K) (by norm_num)
    let A6 : Subgroup (GL (Fin 2 ⊕ Fin 2) K) :=
      ⁅(LargeEvenSpGroup K 2 : Subgroup (GL (Fin 2 ⊕ Fin 2) K)),
        (LargeEvenSpGroup K 2 : Subgroup (GL (Fin 2 ⊕ Fin 2) K))⁆
    have hscal : (LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf A6 = ⊥ := by
      have hcenter : (LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (LargeEvenSpGroup K 2) =
          Subgroup.center ↥(LargeEvenSpGroup K 2) := by
        rw [largeEvenSpGroup_eq_statedSp]
        rw [show StatedSp 2 K = TauCeti.GLSymplectic (Fin 2) K from
          CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2) (K := K)]
        exact (CFSG.ClassicalGroups.Symplectic.center_GLSymplectic_eq (n := 2) (K := K)).symm
      have hbot : Subgroup.center ↥(LargeEvenSpGroup K 2) = ⊥ := hspbot
      have hA6le : A6 ≤ (LargeEvenSpGroup K 2 : Subgroup (GL (Fin 2 ⊕ Fin 2) K)) := by
        refine Subgroup.commutator_le.mpr (fun g hg h hh => ?_)
        rw [commutatorElement_def]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh)
          (Subgroup.inv_mem _ hg)) (Subgroup.inv_mem _ hh)
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hmem : (⟨(x : GL (Fin 2 ⊕ Fin 2) K), hA6le x.2⟩ : ↥(LargeEvenSpGroup K 2)) ∈
          (LargeEvenScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (LargeEvenSpGroup K 2) :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hcenter, hbot, Subgroup.mem_bot] at hmem
      have h1 : (x : GL (Fin 2 ⊕ Fin 2) K) = 1 :=
        congrArg (Subtype.val : ↥(LargeEvenSpGroup K 2) → GL (Fin 2 ⊕ Fin 2) K) hmem
      exact Subtype.ext h1
    have hH : ↥A6 ≃* alternatingGroup (Fin 6) :=
      QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hscal).symm.trans
          (nonempty_b2der_equiv_alternatingGroup (K := K) h42K).some)
    have hcbH : ↥Cb ≃* ↥A6 := by
      have hqA6 : CFSG.Assembly.IsQuasisimple
          ↥⁅(⊤ : Subgroup ↥(StatedSp 2 K)), (⊤ : Subgroup ↥(StatedSp 2 K))⁆ :=
        (isQuasisimple_largeEvenMarking_commutator_of_equiv_statedSp_two h42K
          (T := (⊤ : Subgroup ↥(StatedSp 2 K)))
          (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(StatedSp 2 K)) ≃* ↥(StatedSp 2 K))).1
      have hQperf : ⁅Cb.map eS.toMonoidHom, Cb.map eS.toMonoidHom⁆ = Cb.map eS.toMonoidHom := by
        have h2 := congrArg (Subgroup.map (Cb.map eS.toMonoidHom).subtype)
          hCbmap_component.2.2.1
        rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top,
          Subgroup.range_subtype] at h2
        exact h2
      have hQle : Cb.map eS.toMonoidHom ≤
          ⁅(⊤ : Subgroup ↥(StatedSp 2 K)), (⊤ : Subgroup ↥(StatedSp 2 K))⁆ :=
        calc Cb.map eS.toMonoidHom = ⁅Cb.map eS.toMonoidHom, Cb.map eS.toMonoidHom⁆ := hQperf.symm
          _ ≤ ⁅(⊤ : Subgroup ↥(StatedSp 2 K)), (⊤ : Subgroup ↥(StatedSp 2 K))⁆ :=
            Subgroup.commutator_mono le_top le_top
      have heq : Cb.map eS.toMonoidHom =
          ⁅(⊤ : Subgroup ↥(StatedSp 2 K)), (⊤ : Subgroup ↥(StatedSp 2 K))⁆ :=
        GGHalf.eq_of_isComponentOf_isQuasisimple hqA6
          (CFSG.Assembly.IsComponentOf.of_le_of_le hCbmap_component hQle le_top)
      have hmap : (Cb.map eS.toMonoidHom).map (StatedSp 2 K).subtype = A6 := by
        rw [heq, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
      exact (Subgroup.equivMapOfInjective Cb eS.toMonoidHom eS.injective).trans
        ((Subgroup.equivMapOfInjective (Cb.map eS.toMonoidHom) (StatedSp 2 K).subtype
          (Subgroup.subtype_injective _)).trans (MulEquiv.subgroupCongr hmap))
    have hZ : Subgroup.center ↥A6 = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro z hz
      have hz' : hH z ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
        rw [Subgroup.mem_center_iff]
        intro w
        obtain ⟨w', hw'⟩ := hH.surjective w
        rw [← hw', ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w']
      rw [alternatingGroup.center_eq_bot (α := Fin 6) (by simp), Subgroup.mem_bot] at hz'
      exact hH.injective (by rw [hz', map_one])
    have hXiso : ↥C ⧸ Subgroup.center ↥C ≃* alternatingGroup (Fin 6) :=
      ((QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center ↥Cb)
        (Subgroup.subgroupOfEquivOfLe hCε.1).symm
        (Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hCε.1).symm)).trans
        (QuotientGroup.congr (Subgroup.center ↥Cb)
          (Subgroup.center ↥A6) hcbH
          (Subgroup.map_center_eq hcbH))).trans
        ((QuotientGroup.quotientMulEquivOfEq hZ).trans
          (QuotientGroup.quotientBot.trans hH))
    have hB2 : GGHasLabel (⟨.B2der, 0, 1⟩ : LargeEvenLabel)
        (↥C ⧸ Subgroup.center ↥C) :=
      ggHasLabel_b2der hXiso
    have hB2_lambda : LargeEvenInLambda2 (⟨.B2der, 0, 1⟩ : LargeEvenLabel) := ⟨le_rfl, rfl, rfl⟩
    have hIso := ggLabelRigidInput_holds (⟨.B2der, 0, 1⟩) (⟨.A, d - 1, k'⟩)
      (↥C ⧸ Subgroup.center ↥C) hB2_lambda hA_lambda hB2 hθC
    exact l02qq2spb_not_iso_B2der_A hd hIso
  · have hn1 : 1 ≤ n₁ := by omega
    have hq : CFSG.Assembly.IsQuasisimple ↥(StatedSp n₁ K) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp.isQuasisimple_statedSp_of_not_small
        hn1 (by omega) (by omega)
    have hqtop : CFSG.Assembly.IsQuasisimple (↥(⊤ : Subgroup ↥(StatedSp n₁ K))) :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv Subgroup.topEquiv hq
    have hCbmap : Cb.map eS.toMonoidHom = ⊤ :=
      GGHalf.eq_of_isComponentOf_isQuasisimple hqtop hCbmap_component
    have hCiso : ↥C ≃* ↥(StatedSp n₁ K) :=
      (Subgroup.subgroupOfEquivOfLe hCε.1).symm.trans
        ((Subgroup.equivMapOfInjective Cb eS.toMonoidHom eS.injective).trans
          ((MulEquiv.subgroupCongr hCbmap).trans Subgroup.topEquiv))
    by_cases hn1' : n₁ = 1
    · subst hn1'
      have hf2 : 2 ≤ f := by
        by_contra hlt; push Not at hlt
        have hf1' : f = 1 := by omega
        rw [hf1', pow_one] at hKf
        exact h1s ⟨rfl, hKf⟩
      have eC' : ↥C ≃* ↥(StatedSL 2 K) :=
        (hCiso.trans (CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne K).symm).trans
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
      have eCQSL : ↥C ⧸ Subgroup.center ↥C ≃*
          ↥(StatedSL 2 K) ⧸ Subgroup.center ↥(StatedSL 2 K) :=
        QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center ↥(StatedSL 2 K)) eC'
          (Subgroup.map_center_eq eC')
      have hA1 : GGHasLabel (⟨.A, 1, f⟩ : LargeEvenLabel)
          (↥C ⧸ Subgroup.center ↥C) := by
        unfold GGHasLabel
        rw [show LargeEvenRawDatum (⟨.A, 1, f⟩ : LargeEvenLabel) _ =
            LargeEvenRecipeLinear 2 (2 ^ f) _ from rfl]
        exact ⟨K, inferInstance, inferInstance, hKf,
          ⟨eCQSL.trans (l02qq2spb_statedSLCenterQuotEquivProjective.trans
            (CFSG.StandardType.TypeA.recipeEquiv 2 K).symm)⟩⟩
      have hA1_lambda : LargeEvenInLambda2 (⟨.A, 1, f⟩ : LargeEvenLabel) :=
        ⟨hf1, le_rfl, fun _ => hf2⟩
      have hIso := ggLabelRigidInput_holds (⟨.A, 1, f⟩) (⟨.A, d - 1, k'⟩)
        (↥C ⧸ Subgroup.center ↥C) hA1_lambda hA_lambda hA1 hθC
      exact l02qq2spb_not_iso_A1_Ad hd hIso
    · have hn2 : 2 ≤ n₁ := by omega
      obtain ⟨eX⟩ := nonempty_centerQuot_sp (s := n₁) hn2 (by omega)
        (inferInstance : CharP K 2) hCiso
      have hB : GGHasLabel (⟨.B, n₁, f⟩ : LargeEvenLabel)
          (↥C ⧸ Subgroup.center ↥C) :=
        ggHasLabel_typeB hKf eX
      have hB_lambda : LargeEvenInLambda2 (⟨.B, n₁, f⟩ : LargeEvenLabel) :=
        largeEvenInLambda2_typeB hf1 hn2 (fun h => by
          by_contra hlt; push Not at hlt
          have hf1' : f = 1 := by omega
          rw [hf1', pow_one] at hKf
          exact h42 ⟨h, hKf⟩)
      have hIso := ggLabelRigidInput_holds (⟨.B, n₁, f⟩) (⟨.A, d - 1, k'⟩)
        (↥C ⧸ Subgroup.center ↥C) hB_lambda hA_lambda hB hθC
      exact l02qq2spb_not_iso_B_A hIso
theorem l02qq2spb_unitary_excl {G : Type} [Group G] {d : ℕ} (hd : 3 ≤ d)
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
    {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hEcard : Nat.card E = Q ^ 2)
    {C Blk : Subgroup G}
    (hCε : CFSG.Assembly.IsComponentOf C Blk)
    (eU : ↥Blk ≃* ↥(GUFull m Q E))
    (θC : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K')) :
    False := by
  obtain ⟨k₀, -, hK'0⟩ := @FiniteField.card K' _ (Fintype.ofFinite K') 2 (by infer_instance)
  obtain ⟨k', hk'1, hK'⟩ : ∃ k' : ℕ, 1 ≤ k' ∧ Nat.card K' = 2 ^ k' :=
    ⟨k₀, k₀.pos, by rw [@Nat.card_eq_fintype_card K' (Fintype.ofFinite K'), hK'0]⟩
  have hθC : GGHasLabel (⟨.A, d - 1, k'⟩ : LargeEvenLabel)
      (↥C ⧸ Subgroup.center ↥C) := by
    unfold GGHasLabel
    rw [show LargeEvenRawDatum (⟨.A, d - 1, k'⟩ : LargeEvenLabel) _ =
        LargeEvenRecipeLinear ((d - 1) + 1) (2 ^ k') _ from rfl]
    rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
    exact ⟨K', inferInstance, inferInstance, hK', ⟨θC⟩⟩
  have hA_lambda : LargeEvenInLambda2 (⟨.A, d - 1, k'⟩ : LargeEvenLabel) :=
    ⟨hk'1, by show 1 ≤ d - 1; omega, fun h => by change d - 1 = 1 at h; omega⟩
  let Cb : Subgroup ↥Blk := C.subgroupOf Blk
  have hCb : CFSG.Assembly.IsComponentOf Cb (⊤ : Subgroup ↥Blk) := by
    refine (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := Blk.subtype) (Subgroup.subtype_injective _)).mp ?_
    have hmapCb : Subgroup.map Blk.subtype Cb = C := Subgroup.map_subgroupOf_eq_of_le hCε.1
    simpa only [hmapCb, Subgroup.map_top, Subgroup.range_subtype] using hCε
  have hCbmap_component : CFSG.Assembly.IsComponentOf (Cb.map eU.toMonoidHom)
      (⊤ : Subgroup ↥(GUFull m Q E)) := by
    have htop : (⊤ : Subgroup ↥Blk).map eU.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top]; exact eU.surjective
    have h := isComponentOf_map_mulEquiv eU ((CFSG.Assembly.isComponentOf_iff_open).1 hCb)
    rw [htop] at h
    exact (CFSG.Assembly.isComponentOf_iff_open).2 h
  have hCbGL_component : CFSG.Assembly.IsComponentOf
      ((Cb.map eU.toMonoidHom).map (GUFull m Q E).subtype) (GUFull m Q E) := by
    have := (isComponentOf_map_iff (f := (GUFull m Q E).subtype)
      (Subgroup.subtype_injective _)).mpr hCbmap_component
    simpa only [Subgroup.map_top, Subgroup.range_subtype] using this
  have hCbGL_eq : (Cb.map eU.toMonoidHom).map (GUFull m Q E).subtype = StatedSU m Q E :=
    eq_statedSU_of_isComponentOf_unitaryFull hEcard hCbGL_component
  have hCiso : ↥C ≃* ↥(StatedSU m Q E) :=
    (Subgroup.subgroupOfEquivOfLe hCε.1).symm.trans
      ((Subgroup.equivMapOfInjective Cb eU.toMonoidHom eU.injective).trans
        ((Subgroup.equivMapOfInjective (Cb.map eU.toMonoidHom) (GUFull m Q E).subtype
          (Subgroup.subtype_injective _)).trans
          (MulEquiv.subgroupCongr hCbGL_eq)))
  have hqSU : CFSG.Assembly.IsQuasisimple ↥(StatedSU m Q E) :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv hCiso.symm hCε.2.2
  haveI : Fintype E := Fintype.ofFinite E
  obtain ⟨fU, hQf, hUF⟩ := CFSG.GroupTheory.WeirSylow.exists_unitaryFieldData E (q := Q)
    (by rw [← Nat.card_eq_fintype_card]; exact hEcard)
  have hp2 : ringChar E = 2 := CharP.eq E hUF.charP ‹CharP E 2›
  have hQ2 : Q = 2 ^ fU := by rw [hQf, hp2]
  by_cases hm1 : m ≤ 1
  · exact (ResU3Three.not_isSolvable_of_isQuasisimple hqSU (by
      haveI : Subsingleton ↥(StatedSU m Q E) := by
        have := CFSG.LieType.SemisimpleCentralizers.Held.hct_subsingleton_statedSL_of_le_one
          (K := E) (d := m) hm1
        refine ⟨fun x y => ?_⟩
        have h := Subsingleton.elim (α := ↥(CFSG.Open.StatedSL m E))
          ⟨x.1, CFSG.Open.StatedAPI.statedSU_le_statedSL m Q E x.2⟩
          ⟨y.1, CFSG.Open.StatedAPI.statedSU_le_statedSL m Q E y.2⟩
        exact Subtype.ext
          (congrArg (fun z : ↥(CFSG.Open.StatedSL m E) => (z : GL (Fin m) E)) h)
      infer_instance)).elim
  by_cases hm2 : m = 2
  · subst hm2
    by_cases hQsmall : Q = 2
    · subst hQsmall
      exact (ResU3Three.not_isSolvable_of_isQuasisimple hqSU (by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hcard : Nat.card ↥(StatedSU 2 2 E) = 2 * (2 ^ 2 - 1) :=
          CFSG.RankThree.SubgroupLists.card_statedSU_two (K := E) (r := 2) (f := 1) (by
            rw [hEcard]; norm_num)
        exact CFSG.LieType.SemisimpleCentralizers.Held.hct_isSolvable_of_natCard_eq
          (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
          (by rw [hcard]; norm_num))).elim
    · have hfU2 : 2 ≤ fU := by
        by_contra hlt; push Not at hlt
        interval_cases fU
        · rw [pow_zero] at hQ2
          have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
          rw [hEcard, hQ2] at h2; norm_num at h2
        · rw [pow_one] at hQ2
          exact hQsmall hQ2
      let F' := CFSG.LieType.Steinberg.fixedSubfield E 2 fU
      have hFcard : Nat.card F' = 2 ^ fU :=
        CFSG.LieType.Steinberg.card_fixedSubfield (show Nat.card E = (2 ^ fU) ^ 2 by rw [hEcard, hQ2])
      have hUF2 : UnitaryFieldData 2 fU E := by
        rw [hp2] at hUF
        exact hUF
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨eSL⟩ := CFSG.ClassicalInvolution.Q3.TA3.Q5U3.nonempty_slPart_equiv
        (p := 2) (f := fU) (K := E) hUF2
      have hmem : ∀ A : GL (Fin 2) E,
          A ∈ StatedSU 2 (2 ^ fU) E ↔
            A ∈ CFSG.GH74.GLS.IVK.Proofs2.GU2Stated (2 ^ fU) E ∧
              Matrix.GeneralLinearGroup.det A = 1 := by
        intro A
        rw [show StatedSU 2 (2 ^ fU) E =
              CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 fU E 2 from rfl,
          CFSG.ClassicalGroups.UnitaryFlag.mem_unitarySU_iff hUF2,
          CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.mem_GU2Stated_iff hUF2]
        constructor
        · rintro ⟨hd, hu⟩
          exact ⟨hu, Units.ext (by rw [Matrix.GeneralLinearGroup.val_det_apply, hd]; rfl)⟩
        · rintro ⟨hu, hd⟩
          exact ⟨by rw [← Matrix.GeneralLinearGroup.val_det_apply, hd]; rfl, hu⟩
      let eSU : ↥(CFSG.ClassicalInvolution.Q3.TA3.Q5GL2.slPart
            (CFSG.GH74.GLS.IVK.Proofs2.GU2Stated (2 ^ fU) E)) ≃*
          ↥(StatedSU 2 (2 ^ fU) E) :=
        { toFun := fun A => ⟨((A : ↥(CFSG.GH74.GLS.IVK.Proofs2.GU2Stated (2 ^ fU) E)) :
              GL (Fin 2) E),
            (hmem _).mpr ⟨A.1.2,
              CFSG.ClassicalInvolution.Q3.TA3.Q5GL2.mem_slPart.mp A.2⟩⟩
          invFun := fun B => ⟨⟨B, ((hmem _).mp B.2).1⟩,
            CFSG.ClassicalInvolution.Q3.TA3.Q5GL2.mem_slPart.mpr ((hmem _).mp B.2).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl }
      have eSL2 : ↥(StatedSU 2 (2 ^ fU) E) ≃* Matrix.SpecialLinearGroup (Fin 2) F' :=
        eSU.symm.trans eSL
      have eC2F : ↥C ≃* Matrix.SpecialLinearGroup (Fin 2) F' := by
        rw [hQ2] at hCiso
        exact hCiso.trans eSL2
      have eXSL : ↥C ⧸ Subgroup.center ↥C ≃*
          ↥(StatedSL 2 F') ⧸ Subgroup.center ↥(StatedSL 2 F') :=
        (QuotientGroup.congr (Subgroup.center ↥C)
          (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F')) eC2F
          (Subgroup.map_center_eq eC2F)).trans
        (QuotientGroup.congr (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F'))
          (Subgroup.center ↥(StatedSL 2 F'))
          (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F')
          (Subgroup.map_center_eq (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F')))
      have hA1 : GGHasLabel (⟨.A, 1, fU⟩ : LargeEvenLabel)
          (↥C ⧸ Subgroup.center ↥C) := by
        unfold GGHasLabel
        rw [show LargeEvenRawDatum (⟨.A, 1, fU⟩ : LargeEvenLabel) _ =
            LargeEvenRecipeLinear 2 (2 ^ fU) _ from rfl]
        exact ⟨F', inferInstance, inferInstance, hFcard,
          ⟨eXSL.trans (l02qq2spb_statedSLCenterQuotEquivProjective.trans
            (CFSG.StandardType.TypeA.recipeEquiv 2 F').symm)⟩⟩
      have hA1_lambda : LargeEvenInLambda2 (⟨.A, 1, fU⟩ : LargeEvenLabel) :=
        ⟨by show 1 ≤ fU; omega, le_rfl, fun _ => hfU2⟩
      have hIso := ggLabelRigidInput_holds (⟨.A, 1, fU⟩) (⟨.A, d - 1, k'⟩)
        (↥C ⧸ Subgroup.center ↥C) hA1_lambda hA_lambda hA1 hθC
      exact l02qq2spb_not_iso_A1_Ad hd hIso
  · have hm3 : 3 ≤ m := by omega
    by_cases h32 : m = 3 ∧ Q = 2
    · obtain ⟨hm3', hQ2''⟩ := h32
      exact (ResU3Three.not_isSolvable_of_isQuasisimple hqSU (by
        rw [hm3', hQ2'']
        exact CFSG.Quasithin.isSolvable_statedSU_one (F := E) (by rw [hEcard, hQ2'']; norm_num))).elim
    · have hfU1 : 1 ≤ fU := by
        by_contra hf0; push Not at hf0
        have h0 : fU = 0 := by omega
        rw [h0, pow_zero] at hQ2
        have h2 : 2 ≤ Nat.card E := Finite.one_lt_card
        rw [hEcard, hQ2] at h2; norm_num at h2
      have hcenter : Subgroup.center ↥(StatedSU m Q E) =
          (StatedScalars (Fin m) E).subgroupOf (StatedSU m Q E) := by
        rw [hQ2]
        have hK2 : Nat.card E = (2 ^ fU) ^ 2 := by rw [hEcard, hQ2]
        have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution
          (K := E) (p := 2) (f := fU) hK2
        rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK2 m]
        exact CFSG.ClassicalInvolution.Phan.center_SUid_eq hσ hm3
      have eX : ↥C ⧸ Subgroup.center ↥C ≃* StatedProj (StatedSU m Q E) :=
        (QuotientGroup.congr (Subgroup.center ↥C) (Subgroup.center ↥(StatedSU m Q E)) hCiso
          (Subgroup.map_center_eq hCiso)).trans
          (QuotientGroup.quotientMulEquivOfEq hcenter)
      have htwA : GGHasLabel (⟨.twA, m - 1, fU⟩ : LargeEvenLabel)
          (↥C ⧸ Subgroup.center ↥C) := by
        obtain ⟨b, hb⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
        subst hb
        refine CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.ggHasLabel_twA (E := E) (b := b) (m := fU) ?_ ?_
        · rw [hEcard, hQ2]
        · have eX' := eX
          rw [hQ2] at eX'
          exact eX'
      have htwA_lambda : LargeEvenInLambda2 (⟨.twA, m - 1, fU⟩ : LargeEvenLabel) :=
        CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.largeEvenInLambda2_twA hfU1 (by show 2 ≤ m - 1; omega) (fun h => by
          change m - 1 = 2 at h
          have hm3' : m = 3 := by omega
          subst hm3'
          by_contra hlt; push Not at hlt
          have hfU1' : fU = 1 := by omega
          rw [hfU1'] at hQ2
          exact h32 ⟨rfl, hQ2⟩)
      have hIso := ggLabelRigidInput_holds (⟨.twA, m - 1, fU⟩) (⟨.A, d - 1, k'⟩)
        (↥C ⧸ Subgroup.center ↥C) htwA_lambda hA_lambda htwA hθC
      exact l02qq2spb_not_iso_twA_A hIso

theorem q2Sp_block {d : ℕ} (hd : 3 ≤ d) {K : Type} [Field K] [Finite K] [CharP K 2]
    (b : ↥(LargeEvenSpGroup K d)) (hb : Odd (orderOf b))
    (J₀ : Subgroup (LargeEvenProj (LargeEvenSpGroup K d)))
    (hJ₀ : CFSG.Open.IsComponentOf J₀
      (ggAutFixedSubgroup (MulAut.conj (LargeEvenProjMk (LargeEvenSpGroup K d) b))))
    {K' : Type} [Field K'] [Finite K'] [CharP K' 2]
    (θ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K')) :
    ∃ (m : ℕ) (D : Type) (_ : Field D) (_ : Finite D)
      (ψ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin m) D))
      (π : ↥(Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d))) →* GL (Fin m) D),
      ∀ (h : ↥(Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d)))) (j j' : ↥J₀),
        (j' : LargeEvenProj (LargeEvenSpGroup K d)) =
            LargeEvenProjMk (LargeEvenSpGroup K d) (h : ↥(LargeEvenSpGroup K d)) *
              (j : LargeEvenProj (LargeEvenSpGroup K d)) *
              (LargeEvenProjMk (LargeEvenSpGroup K d) (h : ↥(LargeEvenSpGroup K d)))⁻¹ →
          TableB.linConjAut (Fin m) D (π h) (ψ (QuotientGroup.mk j)) = ψ (QuotientGroup.mk j') := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcenter : Subgroup.center ↥(LargeEvenSpGroup K d) = ⊥ :=
    CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (F := K) (by omega)
  have hπmk_inj : Function.Injective (LargeEvenProjMk (LargeEvenSpGroup K d)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxker : x ∈ (LargeEvenProjMk (LargeEvenSpGroup K d)).ker := hx
    have hle := l02qq2spb_ker_projMk_le_center (LargeEvenSpGroup K d) hxker
    rw [hcenter] at hle
    exact Subgroup.mem_bot.mp hle
  let e : ↥(LargeEvenSpGroup K d) ≃* LargeEvenProj (LargeEvenSpGroup K d) :=
    MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSpGroup K d))
      ⟨hπmk_inj, QuotientGroup.mk'_surjective _⟩
  have hJ₀cent : CFSG.Open.IsComponentOf J₀ (Subgroup.centralizer {e b}) := by
    rwa [ggAutFixedSubgroup_mulAut_conj] at hJ₀
  have hJ₀a : CFSG.Assembly.IsComponentOf J₀ (Subgroup.centralizer {e b}) :=
    (CFSG.Assembly.isComponentOf_iff_open).2 hJ₀cent
  let C : Subgroup ↥(LargeEvenSpGroup K d) := J₀.map e.symm.toMonoidHom
  have hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d))) := by
    have hmap := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
      (f := e.symm.toMonoidHom) e.symm.injective).mpr hJ₀a
    have hc_cent : (Subgroup.centralizer {e b}).map e.symm.toMonoidHom =
        Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d)) := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        apply e.injective
        rw [map_mul, map_mul]
        change e (e.symm y) * e b = e b * e (e.symm y)
        rw [MulEquiv.apply_symm_apply e y]
        exact hy
      · intro hx
        refine ⟨e x, ?_, e.symm_apply_apply x⟩
        simpa only [map_mul] using congrArg e hx
    rwa [hc_cent] at hmap
  have hodd : Odd (orderOf (b : GL (Fin d ⊕ Fin d) K)) := by rwa [Subgroup.orderOf_coe]
  obtain ⟨P, hPprim, hPorth, hPsum, hPcomm, hPsup, hPcard⟩ :=
    centralizer_block_decomp_Sp (b : GL (Fin d ⊕ Fin d) K) b.2 hodd
  have hcent : Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d)) =
      (Subgroup.centralizer {(b : GL (Fin d ⊕ Fin d) K)}).comap (StatedSp d K).subtype := by
    ext g
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subtype.ext_iff, Subgroup.coe_mul]
  rw [hcent, ← hPsup] at hC
  obtain ⟨ε, hε, hCε⟩ := exists_isComponentOf_block P _ hPcomm hC
  let eJC : ↥J₀ ≃* ↥C :=
    Subgroup.equivMapOfInjective J₀ e.symm.toMonoidHom e.symm.injective
  let eCQ : ↥C ⧸ Subgroup.center ↥C ≃* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    (QuotientGroup.congr (Subgroup.center ↥J₀) (Subgroup.center ↥C) eJC
      (Subgroup.map_center_eq eJC)).symm
  rcases blockGroup_iso_Sp_cases (b : GL (Fin d ⊕ Fin d) K) b.2 hodd (hPprim ε hε) with
    ⟨n₁, ⟨eS⟩⟩ | ⟨m, E, hEfield, hEfin, hEchar, ⟨eL⟩⟩ |
      ⟨m, Q, E, hEfield, hEfin, hEchar, hEcard, ⟨eU⟩⟩
  · exact (l02qq2spb_symp_excl hd hCε eS (eCQ.trans θ)).elim
  ·
    let Blk : Subgroup ↥(LargeEvenSpGroup K d) :=
      glBlockCentralizer (StatedSp d K).subtype ({(b : GL (Fin d ⊕ Fin d) K)} : Set (GL (Fin d ⊕ Fin d) K)) ε
    have hsup_sub : (⨆ i : {x // x ∈ P}, glBlockCentralizer (StatedSp d K).subtype
        ({(b : GL (Fin d ⊕ Fin d) K)} : Set (GL (Fin d ⊕ Fin d) K)) i.1) =
        Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d)) :=
      (iSup_subtype' (f := fun (i : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) K) (_ : i ∈ P) =>
        glBlockCentralizer (StatedSp d K).subtype
          ({(b : GL (Fin d ⊕ Fin d) K)} : Set (GL (Fin d ⊕ Fin d) K)) i)).symm.trans
        (hPsup.trans hcent.symm)
    have hle_sub : ∀ i : {x // x ∈ P}, glBlockCentralizer (StatedSp d K).subtype
        ({(b : GL (Fin d ⊕ Fin d) K)} : Set (GL (Fin d ⊕ Fin d) K)) i.1 ≤
        Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d)) :=
      fun i => (le_iSup (fun i : {x // x ∈ P} => glBlockCentralizer (StatedSp d K).subtype
        ({(b : GL (Fin d ⊕ Fin d) K)} : Set (GL (Fin d ⊕ Fin d) K)) i.1) i).trans (le_of_eq hsup_sub)
    have hcomm_sub : ∀ i j : {x // x ∈ P}, i ≠ j →
        ∀ x ∈ glBlockCentralizer (StatedSp d K).subtype
              ({(b : GL (Fin d ⊕ Fin d) K)} : Set (GL (Fin d ⊕ Fin d) K)) i.1,
        ∀ y ∈ glBlockCentralizer (StatedSp d K).subtype
              ({(b : GL (Fin d ⊕ Fin d) K)} : Set (GL (Fin d ⊕ Fin d) K)) j.1, Commute x y :=
      fun i j hij x hx y hy =>
        hPcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) x hx y hy
    have hcard_sub : Nat.card ↥(Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d))) =
        ∏ i : {x // x ∈ P}, Nat.card ↥(glBlockCentralizer (StatedSp d K).subtype
          ({(b : GL (Fin d ⊕ Fin d) K)} : Set (GL (Fin d ⊕ Fin d) K)) i.1) := by
      rw [hcent, hPcard]
      rw [Finset.univ_eq_attach]
      exact (Finset.prod_attach P (fun ε => Nat.card ↥(glBlockCentralizer (StatedSp d K).subtype
        ({(b : GL (Fin d ⊕ Fin d) K)} : Set (GL (Fin d ⊕ Fin d) K)) ε))).symm
    obtain ⟨π_ε, hπ_ε_id, hπ_ε_one⟩ := q2_block_projection
      (fun i : {x // x ∈ P} => glBlockCentralizer (StatedSp d K).subtype
        ({(b : GL (Fin d ⊕ Fin d) K)} : Set (GL (Fin d ⊕ Fin d) K)) i.1)
      (Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d)))
      hle_sub hcomm_sub hsup_sub hcard_sub ⟨ε, hε⟩
    have hnorm : (Blk.subgroupOf (Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d)))).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hle_sub ⟨ε, hε⟩)]
      rw [← hsup_sub]
      refine iSup_le fun i => ?_
      by_cases hi : i.1 = ε
      · subst hi; exact Subgroup.le_normalizer
      · have hcent : glBlockCentralizer (StatedSp d K).subtype
            ({(b : GL (Fin d ⊕ Fin d) K)} : Set (GL (Fin d ⊕ Fin d) K)) i.1 ≤
            Subgroup.centralizer (Blk : Set ↥(LargeEvenSpGroup K d)) := by
          intro y hy
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          exact (hPcomm i.1 i.2 ε hε (fun h => hi h) y hy x hx).symm.eq
        exact hcent.trans (Subgroup.centralizer_le_normalizer _)
    have hconj_blk : ∀ x ∈ Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d)),
        ∀ c ∈ Blk, x * c * x⁻¹ ∈ Blk := by
      intro x hx c hc
      exact (Subgroup.mem_set_normalizer_iff''.mp
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (hle_sub ⟨ε, hε⟩)).mp hnorm (inv_mem hx)) c).mp hc
    let Cb : Subgroup ↥Blk := C.subgroupOf Blk
    have hCb : CFSG.Assembly.IsComponentOf Cb (⊤ : Subgroup ↥Blk) := by
      refine (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
        (f := Blk.subtype) (Subgroup.subtype_injective _)).mp ?_
      have hmapCb : Subgroup.map Blk.subtype Cb = C := Subgroup.map_subgroupOf_eq_of_le hCε.1
      simpa only [hmapCb, Subgroup.map_top, Subgroup.range_subtype] using hCε
    have hCbmap : Cb.map eL.toMonoidHom = StatedSL m E := by
      have htop : (⊤ : Subgroup ↥Blk).map eL.toMonoidHom = ⊤ := by
        rw [Subgroup.map_top, MonoidHom.range_eq_top]; exact eL.surjective
      have h := isComponentOf_map_mulEquiv eL ((CFSG.Assembly.isComponentOf_iff_open).1 hCb)
      rw [htop] at h
      exact eq_statedSL_of_isComponentOf_top ((CFSG.Assembly.isComponentOf_iff_open).2 h)
    let esub : ↥Cb ≃* ↥(StatedSL m E) :=
      (Subgroup.equivMapOfInjective Cb eL.toMonoidHom eL.injective).trans
        (MulEquiv.subgroupCongr hCbmap)
    let eSL : ↥(StatedSL m E) ≃* ↥C :=
      esub.symm.trans (Subgroup.subgroupOfEquivOfLe hCε.1)
    let eSLb : ↥(StatedSL m E) →* ↥Blk := (Subgroup.inclusion hCε.1).comp eSL.toMonoidHom
    have hes_sub : ∀ c : ↥Cb, (esub c : GL (Fin m) E) = eL c := by
      intro c
      simp only [esub, MulEquiv.trans_apply]
      rfl
    have heL_eSLb : ∀ z : ↥(StatedSL m E), eL (eSLb z) = (z : GL (Fin m) E) := by
      intro z
      have h1 : esub (esub.symm z) = z := MulEquiv.apply_symm_apply esub z
      have h2 := hes_sub (esub.symm z)
      rw [h1] at h2
      exact h2.symm
    have hJ₀C : C.map e.toMonoidHom = J₀ := by
      change (J₀.map e.symm.toMonoidHom).map e.toMonoidHom = J₀
      rw [Subgroup.map_map]
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
        ext x; simp
      rw [hcomp, Subgroup.map_id]
    let πJ : ↥C →* ↥J₀ :=
      { toFun := fun c => ⟨e (c : ↥(LargeEvenSpGroup K d)), by
          rw [← hJ₀C]
          exact Subgroup.mem_map.mpr ⟨(c : ↥(LargeEvenSpGroup K d)), c.2, rfl⟩⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := fun a b => by apply Subtype.ext; simp }
    have hπJ_surj : Function.Surjective πJ := by
      intro j
      refine ⟨⟨e.symm (j : LargeEvenProj (LargeEvenSpGroup K d)), ?_⟩, ?_⟩
      · change e.symm (j : LargeEvenProj (LargeEvenSpGroup K d)) ∈ J₀.map e.symm.toMonoidHom
        exact Subgroup.mem_map.mpr ⟨(j : LargeEvenProj (LargeEvenSpGroup K d)), j.2, rfl⟩
      · apply Subtype.ext
        dsimp only [πJ]
        exact MulEquiv.apply_symm_apply e _
    have hπJ_ker : πJ.ker ≤ Subgroup.center ↥C := by
      intro c hc
      rw [MonoidHom.mem_ker] at hc
      rw [Subgroup.mem_center_iff]
      intro d'
      have h1 : (c : ↥(LargeEvenSpGroup K d)) = 1 := by
        apply e.injective
        rw [map_one]
        have h2 : (πJ c : ↥J₀).val = 1 := by rw [hc]; rfl
        dsimp only [πJ] at h2
        exact h2
      have hc1 : c = 1 := Subtype.ext h1
      subst hc1; simp
    let gAB : ↥(StatedSL m E) →* ↥J₀ := πJ.comp eSL.toMonoidHom
    have hgAB_surj : Function.Surjective gAB := hπJ_surj.comp eSL.surjective
    have hker : gAB.ker ≤ Subgroup.center ↥(StatedSL m E) := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hx1 : eSL x ∈ πJ.ker := by rw [MonoidHom.mem_ker]; exact hx
      have hx2 : eSL x ∈ Subgroup.center ↥C := hπJ_ker hx1
      rw [Subgroup.mem_center_iff] at hx2 ⊢
      intro y
      apply eSL.injective
      rw [map_mul, map_mul]
      exact hx2 (eSL y)
    have hQ : CFSG.Assembly.IsQuasisimple ↥(StatedSL m E) :=
      CFSG.Assembly.IsQuasisimple.of_mulEquiv eSL hC.2.2
    have hperf : commutator ↥(StatedSL m E) = ⊤ := hQ.1
    have hperfG : Group.IsPerfect ↥(StatedSL m E) := ⟨hperf⟩
    have hconj_mem : ∀ (A : GL (Fin m) E) (x : ↥(StatedSL m E)),
        A * (x : GL (Fin m) E) * A⁻¹ ∈ StatedSL m E := by
      intro A x
      have hxL : (x : GL (Fin m) E) ∈ LargeEvenSLGroup (Fin m) E := by
        rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL (m)]
        exact x.2
      have h := (inferInstance : (LargeEvenSLGroup (Fin m) E).Normal).conj_mem
        (x : GL (Fin m) E) hxL A
      rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL (m)] at h
      exact h
    let φq : ↥(StatedSL m E) →* ↥J₀ ⧸ Subgroup.center ↥J₀ :=
      (QuotientGroup.mk' (Subgroup.center ↥J₀)).comp gAB
    have hφqsurj : Function.Surjective φq :=
      (QuotientGroup.mk'_surjective (Subgroup.center ↥J₀)).comp hgAB_surj
    have hcomap : (Subgroup.center ↥J₀).comap gAB = Subgroup.center ↥(StatedSL m E) :=
      CFSG.LocalCores.comap_center_eq_of_perfect hperfG gAB hgAB_surj hker
    have hφqker : Subgroup.center ↥(StatedSL m E) = φq.ker := by
      dsimp only [φq]
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
    let ecent : ↥(StatedSL m E) ⧸ Subgroup.center ↥(StatedSL m E) ≃*
        ↥J₀ ⧸ Subgroup.center ↥J₀ :=
      QuotientGroup.liftEquiv (Subgroup.center ↥(StatedSL m E)) (φ := φq) hφqsurj hφqker
    have hecent_mk : ∀ a : ↥(StatedSL m E),
        ecent (QuotientGroup.mk a) = QuotientGroup.mk (gAB a) :=
      fun a => QuotientGroup.liftEquiv_mk (Subgroup.center ↥(StatedSL m E))
        (φ := φq) hφqsurj hφqker a
    let projSL : ↥(StatedSL m E) ⧸ Subgroup.center ↥(StatedSL m E) ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin m) E) :=
      l02qq2spb_statedSLCenterQuotEquivProjective.trans
        (CFSG.StandardType.TypeA.recipeEquiv m E).symm
    let ψ : ↥J₀ ⧸ Subgroup.center ↥J₀ ≃* LargeEvenProj (LargeEvenSLGroup (Fin m) E) :=
      ecent.symm.trans projSL
    let π : ↥(Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d))) →* GL (Fin m) E :=
      eL.toMonoidHom.comp π_ε
    have hblock_conj : ∀ (h : ↥(Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d))))
        (c : ↥Blk),
        (h : ↥(LargeEvenSpGroup K d)) * (c : ↥(LargeEvenSpGroup K d)) *
            (h : ↥(LargeEvenSpGroup K d))⁻¹ =
          (π_ε h : ↥(LargeEvenSpGroup K d)) * (c : ↥(LargeEvenSpGroup K d)) *
            (π_ε h : ↥(LargeEvenSpGroup K d))⁻¹ := by
      intro h c
      have hmem : (h : ↥(LargeEvenSpGroup K d)) * (c : ↥(LargeEvenSpGroup K d)) *
          (h : ↥(LargeEvenSpGroup K d))⁻¹ ∈ Blk := hconj_blk h h.2 c c.2
      have harg : (h * ⟨(c : ↥(LargeEvenSpGroup K d)), hle_sub ⟨ε, hε⟩ c.2⟩ * h⁻¹ :
          ↥(Subgroup.centralizer ({b} : Set ↥(LargeEvenSpGroup K d)))) =
          ⟨(h : ↥(LargeEvenSpGroup K d)) * (c : ↥(LargeEvenSpGroup K d)) *
            (h : ↥(LargeEvenSpGroup K d))⁻¹, hle_sub ⟨ε, hε⟩ hmem⟩ := Subtype.ext rfl
      have h1 : (π_ε ⟨(h : ↥(LargeEvenSpGroup K d)) * (c : ↥(LargeEvenSpGroup K d)) *
            (h : ↥(LargeEvenSpGroup K d))⁻¹, hle_sub ⟨ε, hε⟩ hmem⟩ : ↥Blk) =
          ⟨(h : ↥(LargeEvenSpGroup K d)) * (c : ↥(LargeEvenSpGroup K d)) *
            (h : ↥(LargeEvenSpGroup K d))⁻¹, hmem⟩ :=
        hπ_ε_id ((h : ↥(LargeEvenSpGroup K d)) * (c : ↥(LargeEvenSpGroup K d)) *
          (h : ↥(LargeEvenSpGroup K d))⁻¹) hmem
      have h2 : (π_ε ⟨(h : ↥(LargeEvenSpGroup K d)) * (c : ↥(LargeEvenSpGroup K d)) *
            (h : ↥(LargeEvenSpGroup K d))⁻¹, hle_sub ⟨ε, hε⟩ hmem⟩ : ↥Blk) =
          π_ε h * (π_ε ⟨(c : ↥(LargeEvenSpGroup K d)), hle_sub ⟨ε, hε⟩ c.2⟩) * (π_ε h)⁻¹ := by
        rw [← harg, map_mul, map_mul, map_inv]
      have h3 : (π_ε ⟨(c : ↥(LargeEvenSpGroup K d)), hle_sub ⟨ε, hε⟩ c.2⟩ : ↥Blk) = c :=
        hπ_ε_id (c : ↥(LargeEvenSpGroup K d)) c.2
      exact congrArg (fun x : ↥Blk => (x : ↥(LargeEvenSpGroup K d)))
        (h1.symm.trans (h2.trans (by rw [h3])))
    refine ⟨m, E, hEfield, hEfin, ψ, π, ?_⟩
    intro h j j' hj'
    obtain ⟨x, hx⟩ := hgAB_surj j
    let A : GL (Fin m) E := eL (π_ε h)
    have hπ : π h = A := rfl
    let y' : ↥(StatedSL m E) := ⟨A * (x : GL (Fin m) E) * A⁻¹, hconj_mem A x⟩
    have hy'b : eSLb y' = π_ε h * eSLb x * (π_ε h)⁻¹ := by
      apply eL.injective
      simp only [map_mul, map_inv, heL_eSLb]
      rfl
    have hy'_b : (eSL y' : ↥(LargeEvenSpGroup K d)) =
        (h : ↥(LargeEvenSpGroup K d)) * (eSL x : ↥(LargeEvenSpGroup K d)) *
          (h : ↥(LargeEvenSpGroup K d))⁻¹ := by
      calc (eSL y' : ↥(LargeEvenSpGroup K d))
          = (eSLb y' : ↥(LargeEvenSpGroup K d)) := rfl
        _ = (π_ε h : ↥(LargeEvenSpGroup K d)) * (eSLb x : ↥(LargeEvenSpGroup K d)) *
              (π_ε h : ↥(LargeEvenSpGroup K d))⁻¹ := congrArg Subtype.val hy'b
        _ = (h : ↥(LargeEvenSpGroup K d)) * (eSLb x : ↥(LargeEvenSpGroup K d)) *
              (h : ↥(LargeEvenSpGroup K d))⁻¹ := (hblock_conj h (eSLb x)).symm
        _ = (h : ↥(LargeEvenSpGroup K d)) * (eSL x : ↥(LargeEvenSpGroup K d)) *
              (h : ↥(LargeEvenSpGroup K d))⁻¹ := rfl
    have hgAB_y' : gAB y' = j' := by
      apply Subtype.ext
      change e (eSL y' : ↥(LargeEvenSpGroup K d)) =
        (j' : LargeEvenProj (LargeEvenSpGroup K d))
      rw [hy'_b, map_mul, map_mul, map_inv]
      rw [show e (eSL x : ↥(LargeEvenSpGroup K d)) =
          (j : LargeEvenProj (LargeEvenSpGroup K d)) from congrArg Subtype.val hx]
      exact hj'.symm
    have hψj : ψ (QuotientGroup.mk j) = projSL (QuotientGroup.mk x) := by
      change projSL (ecent.symm (QuotientGroup.mk j)) = projSL (QuotientGroup.mk x)
      have hmkj : QuotientGroup.mk j = ecent (QuotientGroup.mk x) := by
        rw [hecent_mk x, hx]
      rw [hmkj, MulEquiv.symm_apply_apply]
    have hψj' : ψ (QuotientGroup.mk j') = projSL (QuotientGroup.mk y') := by
      change projSL (ecent.symm (QuotientGroup.mk j')) = projSL (QuotientGroup.mk y')
      have hmkj' : QuotientGroup.mk j' = ecent (QuotientGroup.mk y') := by
        rw [hecent_mk y', hgAB_y']
      rw [hmkj', MulEquiv.symm_apply_apply]
    rw [hψj, hψj', hπ]
    have hslconj :
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm y' =
        CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation m E A
          ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm x) :=
      l02qq2spb_specialLinearGroupEquivStatedSL_symm_slConjugation (A := A) (l := x) (l' := y') rfl
    have hprojSL : ∀ z : ↥(StatedSL m E),
        projSL (QuotientGroup.mk z) =
          (CFSG.StandardType.TypeA.recipeEquiv m E).symm
            (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m E
              ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm z)) := by
      intro z
      change (CFSG.StandardType.TypeA.recipeEquiv m E).symm
          (l02qq2spb_statedSLCenterQuotEquivProjective (QuotientGroup.mk z)) = _
      rw [l02qq2spb_statedSLCenterQuotEquivProjective_mk]
    rw [hprojSL x, hprojSL y']
    rw [l02qq2spb_recipeEquiv_symm_linConjAut A
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj m E
        ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL m E).symm x))]
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
    rw [hslconj]
  · exact (l02qq2spb_unitary_excl hd hEcard hCε eU (eCQ.trans θ)).elim

end CFSG.StandardType
