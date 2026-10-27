module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentKnownInputs
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTwInndiagRootBridge
public import CFSG.LocalAnalysis.StandardType.GGMarkingAllInduces
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoverMark
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
public import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreDefs
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.StandardType.GGIrred937TwE6Transport

public section

namespace CFSG.StandardType.TwE6KG7

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.SCFourCover

section BaseChangeHelpers


private theorem kg7base_comm_symm {k K : Type} [Field k] [Field K] (τ : k ≃+* K)
    (σk : k ≃+* k) (σK : K ≃+* K) (hτ : ∀ c, τ (σk c) = σK (τ c)) :
    ∀ c, σk (τ.symm c) = τ.symm (σK c) := by
  intro c
  apply τ.injective
  rw [hτ, τ.apply_symm_apply, τ.apply_symm_apply]

private theorem kg7base_isCompatE6_map {k K : Type} [Field k] [Field K] (τ : k ≃+* K)
    (σk : k ≃+* k) (σK : K ≃+* K) (hτ : ∀ c, τ (σk c) = σK (τ c))
    {b : Fin TwistTag.E6.tag.rank → kˣ} (hb : RecipeExcLang.IsCompatE6 σk.toRingHom b) :
    RecipeExcLang.IsCompatE6 σK.toRingHom
      (fun i => Units.map τ.toRingHom.toMonoidHom (b i)) := by
  intro i
  refine Units.ext ?_
  simp only [hb i, Units.coe_map]
  exact hτ ((b i : kˣ) : k)

private theorem kg7base_baseChangeGL_mem_twInndiag
    {k K : Type} [Field k] [Finite k] [Field K] [Finite K] (τ : k ≃+* K)
    (σk : k ≃+* k) (σK : K ≃+* K) (hτ : ∀ c, τ (σk c) = σK (τ c))
    {w : ModGL TwistTag.E6.tag k} (hw : w ∈ RecipeExcLang.twInndiagGroup k σk) :
    baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom w ∈
      RecipeExcLang.twInndiagGroup K σK := by
  have hle : RecipeExcLang.twInndiagGroup k σk ≤
      (RecipeExcLang.twInndiagGroup K σK).comap
        (baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom) := by
    rw [RecipeExcLang.twInndiagGroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro g (hg | ⟨b, hb, rfl⟩)
    · change baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom g ∈
        RecipeExcLang.twInndiagGroup K σK
      exact RecipeExcLang.graphFixedRootGroup_le_twInndiag σK
        ((map_baseChangeGL_graphFixedRootGroup_le (t := TwistTag.E6) (σ := σk.toRingHom)
          (ι := τ.toRingHom) (Fr := σK.toRingHom) (hσ := σk.surjective)
          (h := fun c => (hτ c).symm)) (Subgroup.mem_map_of_mem _ hg))
    · change baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom
          (rootDiagUnit TwistTag.E6.tag b) ∈
        RecipeExcLang.twInndiagGroup K σK
      rw [baseChangeGL_rootDiagUnit (τ := TwistTag.E6.tag)]
      exact RecipeExcLang.rootDiagUnit_mem_twInndiag
        (kg7base_isCompatE6_map τ σk σK hτ hb)
  exact hle hw

theorem graphFixedRootGroup_map_baseChangeGL_eq
    {k K : Type} [Field k] [Field K] (τ : k ≃+* K) (σk : k ≃+* k) (σK : K ≃+* K)
    (hτ : ∀ c, τ (σk c) = σK (τ c)) :
    (graphFixedRootGroup TwistTag.E6 k σk.toRingHom).map
        (baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom) =
      graphFixedRootGroup TwistTag.E6 K σK.toRingHom := by
  refine le_antisymm ?_ ?_
  · exact map_baseChangeGL_graphFixedRootGroup_le (t := TwistTag.E6) (σ := σk.toRingHom)
      (ι := τ.toRingHom) (Fr := σK.toRingHom) (hσ := σk.surjective)
      (h := fun c => (hτ c).symm)
  · have h2 : (graphFixedRootGroup TwistTag.E6 K σK.toRingHom).map
        (baseChangeGL (τ := TwistTag.E6.tag) τ.symm.toRingHom) ≤
        graphFixedRootGroup TwistTag.E6 k σk.toRingHom :=
      map_baseChangeGL_graphFixedRootGroup_le (t := TwistTag.E6) (σ := σK.toRingHom)
        (ι := τ.symm.toRingHom) (Fr := σk.toRingHom) (hσ := σK.surjective)
        (h := kg7base_comm_symm τ σk σK hτ)
    have hmono := Subgroup.map_mono (f := baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom) h2
    rw [Subgroup.map_map] at hmono
    have hcomp : (baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom).comp
          (baseChangeGL (τ := TwistTag.E6.tag) τ.symm.toRingHom) =
        MonoidHom.id (ModGL TwistTag.E6.tag K) := by
      ext g
      rw [MonoidHom.comp_apply, MonoidHom.id_apply, baseChangeGL_baseChangeGL,
        RingEquiv.toRingHom_comp_symm_toRingHom, baseChangeGL_id]
    rw [hcomp, Subgroup.map_id] at hmono
    exact hmono

private theorem kg7base_congr_twConj
    {k K : Type} [Field k] [Finite k] [Field K] [Finite K] (τ : k ≃+* K)
    (σk : k ≃+* k) (σK : K ≃+* K)
    (e : ↥(graphFixedRootGroup TwistTag.E6 k σk.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 K σK.toRingHom))
    (hcoe : ∀ x, (e x : ModGL TwistTag.E6.tag K) =
      baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom x)
    (hcoesymm : ∀ x, baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom (e.symm x) =
      (x : ModGL TwistTag.E6.tag K))
    (E : ↥(RecipeExcLang.twInndiagGroup k σk) ≃*
      ↥(RecipeExcLang.twInndiagGroup K σK))
    (hE : ∀ w, (E w : ModGL TwistTag.E6.tag K) =
      baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom w)
    (w : ↥(RecipeExcLang.twInndiagGroup k σk)) :
    MulAut.congr e (RecipeExcLang.twConj k σk w) =
      RecipeExcLang.twConj K σK (E w) := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  change (e (RecipeExcLang.twConj k σk w (e.symm x)) : ModGL TwistTag.E6.tag K) =
    (RecipeExcLang.twConj K σK (E w) x : ModGL TwistTag.E6.tag K)
  rw [hcoe, RecipeExcLang.coe_twConj]
  rw [map_mul, map_mul, map_inv, hcoesymm]
  rw [RecipeExcLang.coe_twConj, hE]

end BaseChangeHelpers

theorem exists_twConj_range_baseChange
    {k K : Type} [Field k] [Finite k] [Field K] [Finite K]
    (τ : k ≃+* K) (σk : k ≃+* k) (σK : K ≃+* K) (hτ : ∀ c, τ (σk c) = σK (τ c)) :
    ∃ e : ↥(graphFixedRootGroup TwistTag.E6 k σk.toRingHom) ≃*
        ↥(graphFixedRootGroup TwistTag.E6 K σK.toRingHom),
      ∀ φ, φ ∈ (RecipeExcLang.twConj k σk).range ↔
        MulAut.congr e φ ∈ (RecipeExcLang.twConj K σK).range := by
  classical
  have hC0 := graphFixedRootGroup_map_baseChangeGL_eq τ σk σK hτ
  let e : ↥(graphFixedRootGroup TwistTag.E6 k σk.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 K σK.toRingHom) :=
    (Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.E6 k σk.toRingHom)
      (baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom)
      (baseChangeGL_injective (τ := TwistTag.E6.tag) τ.toRingHom)).trans
        (MulEquiv.subgroupCongr hC0)
  have hcoe : ∀ x, (e x : ModGL TwistTag.E6.tag K) =
      baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom x := fun _ => rfl
  have hcoesymm : ∀ x, baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom (e.symm x) =
      (x : ModGL TwistTag.E6.tag K) := by
    intro x
    exact (hcoe (e.symm x)).symm.trans
      (congrArg Subtype.val (MulEquiv.apply_symm_apply e x))
  let Ehom : ↥(RecipeExcLang.twInndiagGroup k σk) →*
      ↥(RecipeExcLang.twInndiagGroup K σK) :=
    MonoidHom.codRestrict
      ((baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom).comp
        (RecipeExcLang.twInndiagGroup k σk).subtype)
      (RecipeExcLang.twInndiagGroup K σK)
      (fun w => kg7base_baseChangeGL_mem_twInndiag τ σk σK hτ w.2)
  have hEhom_coe : ∀ w, (Ehom w : ModGL TwistTag.E6.tag K) =
      baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom w := fun _ => rfl
  have hEhom_inj : Function.Injective Ehom := by
    intro a b h
    apply Subtype.ext
    apply baseChangeGL_injective (τ := TwistTag.E6.tag) τ.toRingHom
    have h' := congrArg (fun x : ↥(RecipeExcLang.twInndiagGroup K σK) =>
      (x : ModGL TwistTag.E6.tag K)) h
    simpa only [hEhom_coe] using h'
  have hEhom_surj : Function.Surjective Ehom := by
    intro v
    have hv : baseChangeGL (τ := TwistTag.E6.tag) τ.symm.toRingHom
        (v : ModGL TwistTag.E6.tag K) ∈ RecipeExcLang.twInndiagGroup k σk :=
      kg7base_baseChangeGL_mem_twInndiag τ.symm σK σk
        (fun c => (kg7base_comm_symm τ σk σK hτ c).symm) v.2
    refine ⟨⟨baseChangeGL (τ := TwistTag.E6.tag) τ.symm.toRingHom
      (v : ModGL TwistTag.E6.tag K), hv⟩, ?_⟩
    apply Subtype.ext
    rw [hEhom_coe, baseChangeGL_baseChangeGL, RingEquiv.toRingHom_comp_symm_toRingHom,
      baseChangeGL_id]
  let E : ↥(RecipeExcLang.twInndiagGroup k σk) ≃*
      ↥(RecipeExcLang.twInndiagGroup K σK) :=
    MulEquiv.ofBijective Ehom ⟨hEhom_inj, hEhom_surj⟩
  have hE : ∀ w, (E w : ModGL TwistTag.E6.tag K) =
      baseChangeGL (τ := TwistTag.E6.tag) τ.toRingHom w := fun _ => rfl
  refine ⟨e, ?_⟩
  have hrange : (RecipeExcLang.twConj K σK).range =
      (RecipeExcLang.twConj k σk).range.map (MulAut.congr e).toMonoidHom := by
    refine le_antisymm ?_ ?_
    · rintro ψ ⟨v, rfl⟩
      refine Subgroup.mem_map.2 ⟨RecipeExcLang.twConj k σk (E.symm v), ⟨E.symm v, rfl⟩, ?_⟩
      change MulAut.congr e (RecipeExcLang.twConj k σk (E.symm v)) = RecipeExcLang.twConj K σK v
      rw [kg7base_congr_twConj τ σk σK e hcoe hcoesymm E hE (E.symm v),
        MulEquiv.apply_symm_apply]
    · rintro ψ ⟨φ, ⟨w, rfl⟩, rfl⟩
      refine ⟨E w, ?_⟩
      change RecipeExcLang.twConj K σK (E w) = MulAut.congr e (RecipeExcLang.twConj k σk w)
      exact (kg7base_congr_twConj τ σk σK e hcoe hcoesymm E hE w).symm
  intro φ
  rw [hrange]
  constructor
  · intro h
    exact Subgroup.mem_map_of_mem (MulAut.congr e).toMonoidHom h
  · intro h
    obtain ⟨ψ, hψ, hψφ⟩ := Subgroup.mem_map.1 h
    rwa [(MulAut.congr e).injective hψφ] at hψ

end CFSG.StandardType.TwE6KG7
