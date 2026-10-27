module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinearMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FRMat
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotGlobalClass
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotLeviFactFour
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualFRHigher
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotResidualLeviGlue
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotUniqueGen
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.PartOne.S11d.OrthSubfieldDickson
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType.LinearFieldFix

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ
open scoped commutatorElement

variable {d : ℕ} {K : Type} [Field K]

theorem slMapStable (d : ℕ) (K : Type) [Field K] :
    ∀ σ : K ≃+* K, ∀ h ∈ LargeEvenSLGroup (Fin d) K,
      Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ LargeEvenSLGroup (Fin d) K :=
  fun σ h hh => YS09Field.sl_map_mem σ h hh

@[expose] def Induced (σ : K ≃+* K)
    (f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))) : Prop :=
  ∀ x : LargeEvenSLGroup (Fin d) K, f (QuotientGroup.mk x) =
    QuotientGroup.mk (matAct (LargeEvenSLGroup (Fin d) K) (slMapStable d K) σ x)

theorem exists_induced {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) :
    ∃ σ : K ≃+* K, Induced σ f :=
  matField_spec _ (slMapStable d K) hf

variable [Finite K]

@[expose] noncomputable def subfieldInclusion (σ : K ≃+* K) :
    LargeEvenSLGroup (Fin d) (fixF σ) →* LargeEvenSLGroup (Fin d) K where
  toFun A := ⟨Matrix.GeneralLinearGroup.map (fixF σ).subtype A.1,
    (sl_map_subtype_iff σ A.1).2 A.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' A B := Subtype.ext (map_mul _ _ _)

theorem coe_subfieldInclusion (σ : K ≃+* K) (A : LargeEvenSLGroup (Fin d) (fixF σ)) :
    ((subfieldInclusion σ A : LargeEvenSLGroup (Fin d) K) : GL (Fin d) K) =
      Matrix.GeneralLinearGroup.map (fixF σ).subtype A.1 :=
  rfl

@[expose] noncomputable def subfieldHom (σ : K ≃+* K) :
    LargeEvenSLGroup (Fin d) (fixF σ) →* LargeEvenProj (LargeEvenSLGroup (Fin d) K) :=
  (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)).comp (subfieldInclusion σ)

theorem ker_subfieldHom (hd : 1 ≤ d) (σ : K ≃+* K) :
    (subfieldHom (d := d) σ).ker =
      (LargeEvenScalars (Fin d) (fixF σ)).subgroupOf (LargeEvenSLGroup (Fin d) (fixF σ)) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  unfold subfieldHom
  rw [← MonoidHom.comap_ker (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) (subfieldInclusion σ),
    QuotientGroup.ker_mk']
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, coe_subfieldInclusion]
  exact (FR.scalar_iff (fixF σ) (x : GL (Fin d) (fixF σ))).symm

theorem range_subfieldHom (hd : 3 ≤ d) {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    {σ : K ≃+* K} {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))} (hf : Induced σ f) :
    (subfieldHom σ).range = ggFixDer f := by
  classical
  haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let H : Subgroup (GL (Fin d) K) := LargeEvenSLGroup (Fin d) K
  let π : H →* LargeEvenProj H := LargeEvenProjMk H
  let ρ : MulAut H := matAct H (slMapStable d K) σ
  let C : Subgroup H := FP.fixSub ρ
  let D : Subgroup (LargeEvenProj H) := C.map π
  let T : Subgroup (LargeEvenProj H) := FP.fixSub f
  have hInc : (subfieldInclusion σ).range = C := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨A, rfl⟩
      rw [FP.mem_fixSub]
      apply Subtype.ext
      change ((ρ (subfieldInclusion σ A) : H) : GL (Fin d) K) =
        ((subfieldInclusion σ A : H) : GL (Fin d) K)
      rw [matAct_coe H (slMapStable d K) σ (subfieldInclusion σ A), coe_subfieldInclusion]
      exact glMap_subtype_fixed σ A.1
    · intro x hx
      rw [FP.mem_fixSub] at hx
      rw [MonoidHom.mem_range]
      have hfix : Matrix.GeneralLinearGroup.map σ.toRingHom (x : GL (Fin d) K) =
          (x : GL (Fin d) K) := by
        rw [← matAct_coe H (slMapStable d K) σ x]
        exact congrArg (fun y : H => (y : GL (Fin d) K)) hx
      obtain ⟨A, hA⟩ := exists_descend σ (x : GL (Fin d) K) hfix
      refine ⟨⟨A, ?_⟩, ?_⟩
      · apply (sl_map_subtype_iff σ A).1
        rw [hA]
        exact x.2
      · apply Subtype.ext
        rw [coe_subfieldInclusion]
        exact hA
  have hRange : (subfieldHom σ).range = D := by
    unfold subfieldHom
    rw [MonoidHom.range_comp, hInc]
  have hZc : (LargeEvenScalars (Fin d) K).subgroupOf H ≤ Subgroup.center H :=
    scalars_subgroupOf_le_center H
  have hZodd : Odd (Nat.card ((LargeEvenScalars (Fin d) K).subgroupOf H)) :=
    scalars_subgroupOf_odd hm hK H
  have hmem : ∀ x : H, f (QuotientGroup.mk x) = QuotientGroup.mk (ρ x) := hf
  obtain ⟨hDT, hcomm, -⟩ := FR.subfield_core ((LargeEvenScalars (Fin d) K).subgroupOf H)
    hZc hZodd ρ f hmem
  haveI hperf : Group.IsPerfect ↥(LargeEvenSLGroup (Fin d) (fixF σ)) :=
    Subgroup.isPerfect_iff.2 (commutator_slGroup (K := fixF σ) hd)
  have hDperf : Group.IsPerfect ↥D := by
    have h1 : Group.IsPerfect ↥((subfieldHom (d := d) σ).range) :=
      Group.IsPerfect.range (subfieldHom (d := d) σ)
    rwa [hRange] at h1
  have hT : ggFixSub f = T := Subgroup.ext fun _ => Iff.rfl
  rw [hRange]
  unfold ggFixDer
  rw [hT]
  refine le_antisymm ?_ hcomm
  · haveI := hDperf
    rw [← Subgroup.commutator_eq_self (H := D)]
    exact Subgroup.commutator_mono hDT hDT

@[expose] noncomputable def subfieldEquiv (hd : 3 ≤ d) {m : ℕ} (hm : 1 ≤ m)
    (hK : Nat.card K = 2 ^ m) {σ : K ≃+* K}
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))} (hf : Induced σ f) :
    LargeEvenProj (LargeEvenSLGroup (Fin d) (fixF σ)) ≃* ggFixDer f :=
  ((QuotientGroup.quotientMulEquivOfEq (ker_subfieldHom (by omega) σ).symm).trans
    (QuotientGroup.quotientKerEquivRange (subfieldHom σ))).trans
    (MulEquiv.subgroupCongr (range_subfieldHom hd hm hK hf))

theorem coe_subfieldEquiv_mk (hd : 3 ≤ d) {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    {σ : K ≃+* K} {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))} (hf : Induced σ f)
    (A : LargeEvenSLGroup (Fin d) (fixF σ)) :
    ((subfieldEquiv hd hm hK hf (QuotientGroup.mk A) : ggFixDer f) :
        LargeEvenProj (LargeEvenSLGroup (Fin d) K)) = subfieldHom σ A :=
  rfl

end CFSG.StandardType.LinearFieldFix

end
