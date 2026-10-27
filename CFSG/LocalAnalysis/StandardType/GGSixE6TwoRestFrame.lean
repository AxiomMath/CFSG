module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYRoots
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

open scoped Pointwise

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

@[expose] def stdQRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | IsRoot .E6 γ ∧ 0 < iform γ E6Pilot.yLamAS}

@[expose] def stdZRoots : Set (Fin Tag.E6.rank → ℤ) :=
  {γ | IsRoot .E6 γ ∧ iform γ E6Pilot.yLamAS = 2}

@[expose] noncomputable def qStd :
    Subgroup EC :=
  (rootSpan .E6 F2 stdQRoots).subgroupOf (adjointGroup .E6 F2)

@[expose] noncomputable def z0Std :
    Subgroup EC :=
  (rootSpan .E6 F2 stdZRoots).subgroupOf (adjointGroup .E6 F2)

@[expose] noncomputable def wQ : WeylGroup .E6 :=
  weylOfWord .E6 [0, 2, 5, 4, 3, 1]

@[expose] noncomputable def nQ : EC :=
  ⟨canonicalRep (coxeterSystem .E6) F2 wQ, canonicalRep_mem_adjointGroup _ F2 wQ⟩

private theorem e6rf_map_subgroupOf_conj {G : Type*} [Group G] {H A : Subgroup G} (hH : H ≤ A)
    (g : A) :
    (H.subgroupOf A).map (MulAut.conj g).toMonoidHom =
      (H.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf A := by
  change (MulAut.conj g) • (H.subgroupOf A) = (MulAut.conj (g : G) • H).subgroupOf A
  rw [Subgroup.conj_smul_subgroupOf hH g]

theorem wQ_smul_yLamAS : wQ • E6Pilot.yLamAS = lamE := by
  have hframe : ([Tag.E6.rootCertificate.root 61, Tag.E6.rootCertificate.root 62] :
      List (Fin Tag.E6.rank → ℤ)) = oddDerivE6YFrame := by decide +kernel
  have hy : E6Pilot.yLamAS =
      Tag.E6.rootCertificate.root 61 + Tag.E6.rootCertificate.root 62 := by
    rw [E6Pilot.yLamAS_check.2, ← hframe]
    simp
  have h61 : wQ • Tag.E6.rootCertificate.root 61 =
      Tag.E6.rootCertificate.root (wordPos Tag.E6.rootCertificate [0, 2, 5, 4, 3, 1] 61) := by
    rw [wQ, ← (wordPos_spec (Tag.rootCertificate_check .E6) [0, 2, 5, 4, 3, 1]
      (by decide +kernel)).2]
  have h62 : wQ • Tag.E6.rootCertificate.root 62 =
      Tag.E6.rootCertificate.root (wordPos Tag.E6.rootCertificate [0, 2, 5, 4, 3, 1] 62) := by
    rw [wQ, ← (wordPos_spec (Tag.rootCertificate_check .E6) [0, 2, 5, 4, 3, 1]
      (by decide +kernel)).2]
  calc wQ • E6Pilot.yLamAS
      = wQ • (Tag.E6.rootCertificate.root 61 + Tag.E6.rootCertificate.root 62) := by rw [hy]
    _ = wQ • Tag.E6.rootCertificate.root 61 + wQ • Tag.E6.rootCertificate.root 62 := smul_add ..
    _ = Tag.E6.rootCertificate.root (wordPos Tag.E6.rootCertificate [0, 2, 5, 4, 3, 1] 61) +
        Tag.E6.rootCertificate.root (wordPos Tag.E6.rootCertificate [0, 2, 5, 4, 3, 1] 62) := by
          rw [h61, h62]
    _ = lamE := RootCertificate.eq_of_ofFn_beq (by decide +kernel)

theorem image_wQ_stdQRoots :
    (fun γ => wQ • γ) '' stdQRoots = qRoots := by
  rw [stdQRoots, qRoots,
    E6Pilot.image_smul_setOf_iform wQ E6Pilot.yLamAS (fun n => 0 < n), wQ_smul_yLamAS]

theorem image_wQ_stdZRoots :
    (fun γ => wQ • γ) '' stdZRoots = zRoots := by
  rw [stdZRoots, zRoots,
    E6Pilot.image_smul_setOf_iform wQ E6Pilot.yLamAS (fun n => n = 2), wQ_smul_yLamAS]

theorem conj_nQ_xr
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) :
    nQ * xr β * nQ⁻¹ = xr (wQ • β) := by
  apply Subtype.ext
  change canonicalRep (coxeterSystem .E6) F2 wQ * pinnedX .E6 F2 β 1 *
      (canonicalRep (coxeterSystem .E6) F2 wQ)⁻¹ = pinnedX .E6 F2 (wQ • β) 1
  exact E6Pilot.canonicalRep_mul_pinnedX_mul_inv_of_charTwo wQ hβ 1

theorem qE_eq_map_qStd :
    qE = qStd.map (MulAut.conj nQ).toMonoidHom := by
  have hstd : ∀ α ∈ stdQRoots, IsRoot .E6 α := fun α hα => hα.1
  rw [qE, qStd, e6rf_map_subgroupOf_conj (E6Pilot.rootSpan_le_adjointGroup_E6 stdQRoots) nQ]
  congr 1
  rw [show (nQ : ModGL .E6 F2) = canonicalRep (coxeterSystem .E6) F2 wQ from rfl,
    (canonical_weyl_root_transport .E6 F2).1 wQ stdQRoots hstd, image_wQ_stdQRoots]

theorem z0E_eq_map_z0Std :
    z0E = z0Std.map (MulAut.conj nQ).toMonoidHom := by
  have hstd : ∀ α ∈ stdZRoots, IsRoot .E6 α := fun α hα => hα.1
  rw [z0E, z0Std, e6rf_map_subgroupOf_conj (E6Pilot.rootSpan_le_adjointGroup_E6 stdZRoots) nQ]
  congr 1
  rw [show (nQ : ModGL .E6 F2) = canonicalRep (coxeterSystem .E6) F2 wQ from rfl,
    (canonical_weyl_root_transport .E6 F2).1 wQ stdZRoots hstd, image_wQ_stdZRoots]

end CFSG.StandardType.GGSixE6Two
