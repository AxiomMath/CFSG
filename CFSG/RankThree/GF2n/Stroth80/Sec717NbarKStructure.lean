module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerModelDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec714ModelStable
import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSetupOfModel
import CFSG.RankThree.GF2n.Stroth80.Sec717LayersRoot
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveRep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement


theorem sec717NbarKStructure_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (h52a : Stroth52aStatement) (h52b : Stroth52bStatement)
    (hNO : Sec7NOrderStatement) (hZcard : Sec7ZCardStatement) (hCRW : Sec7CRWStatement)
    (hMp : Sec7CentreMpStatement) (hA : Sec7AExistsStatement) (hZV : Sec7ZVStatement) :
    Sec717NbarKStructureStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 m γ M₀ hM φ hφπ T hT g hg c
  classical
  haveI : FiniteDimensional (GaloisField 2 m) M₀.E := M₀.fin
  have h310chi : Stroth310ChiStatement := stroth310Chi_of_34 h34
  obtain ⟨ρ, b, hS⟩ := hc.exists_isTensorSetup h34 hs.toSec5.width hs.toSec5.n_gt
    hs.toSec5.noA2 hs.toSec5.gen hM
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hVtQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hρφ : ∀ (x : ↥(bar M Q (H0 M Z))) (e : M₀.E), (ρ (x : Mbar M Q)).toAdd e = φ x e := by
    intro x e
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
    have hyx : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z) := hy ▸ x.2
    have hxy : x = ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hyx⟩ := Subtype.ext hy.symm
    subst hxy
    have key := eq_of_pi_conj_eq (M₀ := M₀) (g := (y : G))
      (S₁ := fun e => (ρ (QuotientGroup.mk y)).toAdd e)
      (S₂ := fun e => φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hyx⟩ e)
      (fun x hx => hS.conj y x hx) (fun x hx => hφπ y hyx x hx)
    exact congrFun key e
  have hTset := hc.sec717_T_eq_image hZcard hMp hZV hs hZ0 M₀ φ hφπ T hT
  have hmemT : ∀ e, e ∈ T ↔ e ∈ hc.VtSub hS.model t := by
    intro e
    rw [Ctx.mem_VtSub, Tim79.QuadModel.mem_img]
    have : e ∈ (T : Set M₀.E) ↔ e ∈ M₀.π '' (Vt M (LB M Q B) B Z t : Set G) := by rw [hTset]
    rw [SetLike.mem_coe] at this
    rw [this]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hVtQ hx, rfl⟩
    · rintro ⟨x, hx, -, rfl⟩
      exact ⟨x, hx, rfl⟩
  have hmemP : ∀ e, e ∈ M₀.B.orthogonal T ↔ e ∈ S714.wsub hS t := by
    intro e
    rw [LinearMap.BilinForm.mem_orthogonal_iff, S714.mem_wsub,
      mem_img_Wt_iff M₀ hS.model.reg hVtQ]
    constructor
    · intro h v hv
      have h1 := h v ((hmemT v).mpr hv)
      rw [Tim79.QuadModel.B_comm] at h1
      exact neg_eq_zero.mp h1
    · intro h v hv
      rw [Tim79.QuadModel.B_comm, h v ((hmemT v).mp hv), neg_zero]
  have hopm : ∀ (x : ↥(bar M Q (H0 M Z))) (e : M₀.E),
      opm (φ x) e = S714.dmap ρ (x : Mbar M Q) e := by
    intro x e
    rw [opm_apply, S714.dmap, hρφ]
  have hadj : ∀ (x : ↥(bar M Q (H0 M Z))), (x : Mbar M Q) ∈ bar M Q (hc.CN t) →
      ∀ (e w : M₀.E), w ∈ S714.wsub hS t →
        M₀.B (S714.dmap ρ (x : Mbar M Q) e) w = - M₀.B e (S714.dmap ρ (x : Mbar M Q) w) := by
    intro x hx e w hw
    obtain ⟨-, hmid, htop⟩ := S714.dmap_CN_facts h310chi h52a hS hs hr hx
    have hiso := hS.iso (x : Mbar M Q) x.2 e w
    rw [S714.act_eq_add_dmap, S714.act_eq_add_dmap] at hiso
    have h0 : M₀.B (S714.dmap ρ (x : Mbar M Q) e) (S714.dmap ρ (x : Mbar M Q) w) = 0 :=
      S714.bilin_wsub_vsub hS t (htop e) (hmid w hw)
    simp only [map_add, LinearMap.add_apply, h0, add_zero] at hiso
    linear_combination hiso
  have hgN : (g : Mbar M Q) ∈ bar M Q (hc.CN t) := Subgroup.mem_subgroupOf.mp hg
  obtain ⟨g', hg', hΔ⟩ := S714.exists_delta_smul h34 hRoot h310chi h51 h52a h52b hNO hZcard
    hCRW hMp hS hs hr hgN c
  let x' : ↥(bar M Q (H0 M Z)) := ⟨g', S714.mem_bar_H0_of_CN hg'⟩
  have hx'N : (x' : Mbar M Q) ∈ bar M Q (hc.CN t) := hg'
  refine ⟨x', Subgroup.mem_subgroupOf.mpr hg', ?_⟩
  have hmid : ∀ w ∈ M₀.B.orthogonal T, (opm (φ x') - c • opm (φ g)) w = 0 := by
    intro w hw
    have hw' := (hmemP w).mp hw
    have h1 := LinearMap.congr_fun hΔ ⟨w, hw'⟩
    rw [LinearMap.smul_apply, S714.delta_apply, S714.delta_apply] at h1
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hopm, hopm]
    exact sub_eq_zero.mpr h1
  refine ⟨fun e => ?_, hmid⟩
  obtain ⟨hnd, hrefl, -⟩ := quadModel_form_facts M₀
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl T,
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  have hw' := (hmemP w).mp hw
  have hFw := hmid w hw
  rw [LinearMap.sub_apply, LinearMap.smul_apply, hopm, hopm] at hFw
  rw [Tim79.QuadModel.B_comm, neg_eq_zero, LinearMap.sub_apply,
    LinearMap.smul_apply, hopm, hopm, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, hadj x' hx'N e w hw', hadj g hgN e w hw', smul_eq_mul]
  have e1 : S714.dmap ρ (x' : Mbar M Q) w = c • S714.dmap ρ (g : Mbar M Q) w :=
    sub_eq_zero.mp hFw
  rw [e1, map_smul, smul_eq_mul]
  ring

end CFSG.RankThree.GF2n.Stroth80
