module

public import CFSG.LocalAnalysis.StandardType.ExcPay.Defs

import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeU
import CFSG.LocalAnalysis.StandardType.GGLieCoreLang
import CFSG.LocalAnalysis.SeitzReduction.E7PilotMainSetup
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.FieldCopy
import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
import CFSG.LocalAnalysis.StandardType.GGFinModelRat
import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
import CFSG.LieType.AschbacherSeitz.RootGroupTransport
import CFSG.RankThree.PartOne.Q1327T.Item7D4W
import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Levi
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatAssembly
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatEvenOuterOmegaExc

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.Q1327T
  CFSG.LieType.Universal CFSG.LieType.Steinberg.Minuscule CFSG.LieType.CurtisTits
  CFSG.LieType.AschbacherSeitz
  CFSG.StandardType CFSG.StandardType.LieCore
  CFSG.StandardType.GGFinModel CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


private theorem excPayM_model_eq_ratPoints_map {p f : ℕ} {ht : GGExcFive .E7}
    (M : GGDatumModel .E7 f p ht) :
    M.D.model = (ratPoints M.D.Φ).map (MulAut.conj M.D.g0⁻¹).toMonoidHom := by
  apply le_antisymm
  · rintro y hy
    rw [LangDatum.mem_model] at hy
    obtain ⟨hyG, hyfix⟩ := hy
    change M.D.n * M.D.Φ y * M.D.n⁻¹ = y at hyfix
    rw [Subgroup.mem_map]
    refine ⟨M.D.g0 * y * M.D.g0⁻¹, ?_, ?_⟩
    · rw [ratPoints, Subgroup.mem_inf]
      refine ⟨mul_mem (mul_mem M.D.g0_mem hyG) (inv_mem M.D.g0_mem), ?_⟩
      change M.D.Φ (M.D.g0 * y * M.D.g0⁻¹) = M.D.g0 * y * M.D.g0⁻¹
      rw [map_mul, map_mul, map_inv, M.D.lang]
      calc (M.D.g0 * M.D.n) * M.D.Φ y * (M.D.g0 * M.D.n)⁻¹
          = M.D.g0 * (M.D.n * M.D.Φ y * M.D.n⁻¹) * M.D.g0⁻¹ := by group
        _ = M.D.g0 * y * M.D.g0⁻¹ := by rw [hyfix]
    · change M.D.g0⁻¹ * (M.D.g0 * y * M.D.g0⁻¹) * M.D.g0 = y
      group
  · rintro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [ratPoints, Subgroup.mem_inf] at hx
    obtain ⟨hxG, hxfix⟩ := hx
    change M.D.Φ x = x at hxfix
    have hconj : ∀ z : ModGL (langTag .E7) GGL, (MulAut.conj M.D.g0⁻¹).toMonoidHom z =
        M.D.g0⁻¹ * z * M.D.g0 := fun z => by
      show MulAut.conj M.D.g0⁻¹ z = M.D.g0⁻¹ * z * M.D.g0
      rw [MulAut.conj_apply, inv_inv]
    rw [LangDatum.mem_model]
    refine ⟨mul_mem (mul_mem (inv_mem M.D.g0_mem) hxG) M.D.g0_mem, ?_⟩
    change M.D.n * M.D.Φ ((MulAut.conj M.D.g0⁻¹).toMonoidHom x) *
      M.D.n⁻¹ = (MulAut.conj M.D.g0⁻¹).toMonoidHom x
    rw [hconj, map_mul, map_mul, map_inv, hxfix, M.D.lang]
    group

private theorem excPayM_ratPoints_eq_image {p f : ℕ} {ht : GGExcFive .E7} (hf : 1 ≤ f)
    (M : GGDatumModel .E7 f p ht) :
    ratPoints (ggPhi .E7 f) = (adjointGroup .E7 (GaloisField 2 f)).map
      (baseChangeGL (ggRatEmb f)) := by
  let K := GaloisField 2 f
  let L := GGL
  letI : Algebra K L := (ggRatEmb f).toAlgebra
  have hKcard : Nat.card K = 2 ^ f := GaloisField.card 2 f (by omega)
  have hFr : ∀ c : L, ggFrobT f c = c ^ Nat.card K := fun c => by
    rw [hKcard]
    exact ggFrobT_apply f c
  have hbij : Function.Bijective (ggFrobT f) := bijective_iterateFrobenius GGL 2 f
  change (ratPoints (ggPhi .E7 f) : Subgroup (ModGL Tag.E7 GGL)) =
    (adjointGroup Tag.E7 (GaloisField 2 f)).map (baseChangeGL (ggRatEmb f))
  apply le_antisymm
  · intro g hg
    unfold ratPoints at hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgG, hgfix⟩ := hg
    have h :=
      CFSG.HardMathSupport.C14ExcBridgeU.mem_map_baseChange_of_frobenius_fixed_E7_of_bijective
      (K := K) (L := L) (Fr := ggFrobT f) hFr hbij (g := g) hgG hgfix
    simpa [K, L, RingHom.algebraMap_toAlgebra] using h
  · intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    unfold ratPoints
    rw [Subgroup.mem_inf]
    constructor
    · exact CFSG.SeitzReduction.E7Pilot.baseChangeGL_mem_adjointGroup_of_E7
        (ggRatEmb f) ⟨x, hx⟩
    · change Units.map (entrywiseHom (ggFrobT f)) (baseChangeGL (ggRatEmb f) x) =
        baseChangeGL (ggRatEmb f) x
      have hcomp : (ggFrobT f).comp (ggRatEmb f) = ggRatEmb f := by
        ext c
        rw [RingHom.comp_apply, ggFrobT_apply]
        have hmem : ggRatEmb f c ∈ Set.range (ggRatEmb f) := ⟨c, rfl⟩
        rw [ggRatEmb_range hf] at hmem
        exact hmem
      rw [CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
        CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]

theorem datumModel_Γ_eq_model_E7 {p f : ℕ} {ht : GGExcFive .E7} (hf : 1 ≤ f)
    (M : GGDatumModel .E7 f p ht) : M.D.Γ = M.D.model := by
  haveI hsc : Group.IsPerfect ↥(e7Data_valid.minGroup (GaloisField 2 f)) :=
    CFSG.LieType.CurtisTits.isPerfect_e7 (GaloisField 2 f)
  haveI : Group.IsPerfect (adjointGroup .E7 (GaloisField 2 f)) :=
    Group.IsPerfect.ofSurjective (f := (e7EquivAlg f).toMonoidHom) (e7EquivAlg f).surjective
  have hImagePerf : Group.IsPerfect ↥((adjointGroup .E7 (GaloisField 2 f)).map
      (baseChangeGL (ggRatEmb f))) := by
    rw [← Subgroup.range_subtype (adjointGroup .E7 (GaloisField 2 f))]
    rw [← MonoidHom.range_comp]
    exact Group.IsPerfect.range ((baseChangeGL (ggRatEmb f)).comp
      (adjointGroup .E7 (GaloisField 2 f)).subtype)
  have hRatPointsPerf : Group.IsPerfect ↥(ratPoints (ggPhi .E7 f)) := by
    rw [excPayM_ratPoints_eq_image hf M]
    exact hImagePerf
  have hRatPointsPerf' : Group.IsPerfect ↥(ratPoints M.D.Φ) := by
    rw [M.hΦ]
    exact hRatPointsPerf
  have hModelPerf : Group.IsPerfect ↥M.D.model := by
    rw [excPayM_model_eq_ratPoints_map M]
    rw [← Subgroup.range_subtype (ratPoints M.D.Φ)]
    rw [← MonoidHom.range_comp]
    letI : Group.IsPerfect ↥(ratPoints M.D.Φ) := hRatPointsPerf'
    exact Group.IsPerfect.range ((MulAut.conj M.D.g0⁻¹).toMonoidHom.comp
      (ratPoints M.D.Φ).subtype)
  have : Group.IsPerfect ↥M.D.model := hModelPerf
  simpa only [LangDatum.Γ] using (Subgroup.commutator_eq_self (H := M.D.model))

theorem canonicalRep_simple_mem_model_E7 {p f : ℕ} {ht : GGExcFive .E7} (hp2 : p ≠ 2)
    (hplus : p ∣ 2 ^ f + 1) (M : GGDatumModel .E7 f p ht) (k : Fin (langTag .E7).rank) :
    canonicalRep (coxeterSystem (langTag .E7)) GGL (simple (langTag .E7) k) ∈ M.D.model := by
  let n_k := canonicalRep (coxeterSystem (langTag .E7)) GGL (simple (langTag .E7) k)
  have hmem_adj : n_k ∈ adjointGroup .E7 GGL :=
    canonicalRep_mem_adjointGroup (coxeterSystem (langTag .E7)) GGL (simple (langTag .E7) k)
  have hbij : Function.Bijective (ggFrobT f) := bijective_iterateFrobenius GGL 2 f
  let σ : GGL ≃+* GGL := RingEquiv.ofBijective (ggFrobT f) hbij
  have hσ : σ.toRingHom = ggFrobT f := rfl
  have hΦ_fix : M.D.Φ n_k = n_k := by
    rw [M.hΦ]
    rw [show ggPhi .E7 f = Units.map (entrywiseHom (ggFrobT f)) from rfl]
    rw [← hσ]
    exact entrywise_canonicalRep σ (simple (langTag .E7) k)
  have hw_smul : ∀ u : Fin (langTag .E7).rank → ℤ, M.w • u = eps p f • u := by
    intro u
    have h := M.hw u
    simp only [ggGraphLat, piB_E7, id_eq] at h
    convert h using 1
    congr 1
  have hw_comm_simple : ∀ k, M.w * simple (langTag .E7) k = simple (langTag .E7) k * M.w := by
    intro k
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Fin (langTag .E7).rank → ℤ)
    intro u
    calc (M.w * simple (langTag .E7) k) • u
        = M.w • (simple (langTag .E7) k • u) := by rw [mul_smul]
      _ = eps p f • (simple (langTag .E7) k • u) := by rw [hw_smul]
      _ = simple (langTag .E7) k • (eps p f • u) := by
          rw [smul_comm]
      _ = simple (langTag .E7) k • (M.w • u) := by rw [hw_smul]
      _ = (simple (langTag .E7) k * M.w) • u := by rw [mul_smul]
  have hcomm : M.D.n * n_k = n_k * M.D.n := by
    rw [M.hn]
    rw [← canonicalRep_mul_charTwo, ← canonicalRep_mul_charTwo]
    congr 1
    exact hw_comm_simple k
  rw [LangDatum.mem_model]
  refine ⟨hmem_adj, ?_⟩
  change M.D.n * M.D.Φ n_k * M.D.n⁻¹ = n_k
  rw [hΦ_fix]
  rw [mul_inv_eq_iff_eq_mul]
  exact hcomm

end CFSG.StandardType.ExcPay
