module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGNsq2QuotHyp
import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
import CFSG.Assembly.Subnormal
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem NsQuot.Datum.exists_isComponentOf_img {G : Type} [Group G] [Finite G] {Q : Type}
    [Group Q] {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}
    (hD : NsQuot.Datum p N f L Bs Z) {x : G} (hx : x ∈ N)
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) {J : Subgroup G}
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer ({x} : Set G))) :
    ∃ J' : Subgroup Q,
      IsComponentOf J' (NsQuot.img N f L ⊓ Subgroup.centralizer ({f ⟨x, hx⟩} : Set Q)) ∧
        Nonempty (↥J' ⧸ Subgroup.center ↥J' ≃* ↥J ⧸ Subgroup.center ↥J) := by
  classical
  have hJL : J ≤ L := hJ.1.trans inf_le_left
  have hJN : J ≤ N := hJL.trans hD.LN
  have hCle : NsQuot.img N f (L ⊓ Subgroup.centralizer ({x} : Set G)) ≤
      NsQuot.img N f L ⊓ Subgroup.centralizer ({f ⟨x, hx⟩} : Set Q) := by
    intro q hq
    obtain ⟨u, hu, rfl⟩ := NsQuot.mem_img.1 hq
    refine Subgroup.mem_inf.2 ⟨NsQuot.mem_img.2 ⟨u, (Subgroup.mem_inf.1 hu).1, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : u * (⟨x, hx⟩ : ↥N) = ⟨x, hx⟩ * u :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hu).2)
    rw [← map_mul, ← map_mul, hcomm]
  have hnorm : ((NsQuot.img N f (L ⊓ Subgroup.centralizer ({x} : Set G))).subgroupOf
      (NsQuot.img N f L ⊓ Subgroup.centralizer ({f ⟨x, hx⟩} : Set Q))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCle]
    intro c q hc hq
    obtain ⟨u, hu, rfl⟩ := NsQuot.mem_img.1 hc
    obtain ⟨l, hl, rfl⟩ := NsQuot.mem_img.1 (Subgroup.mem_inf.1 hq).1
    have hq2 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hq).2
    have huL : (u : G) ∈ L := (Subgroup.mem_inf.1 hu).1
    have hxu : x * (u : G) = (u : G) * x :=
      (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hu).2).symm
    have hxl : (⟨x, hx⟩ : ↥N) * l * (⟨x, hx⟩ : ↥N)⁻¹ * l⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← hq2]
      group
    have hz : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ Z := (hD.mem_ker_iff _).1 hxl
    have hw : (l : G) * u * (l : G)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hl huL) (L.inv_mem hl)
    have hzc := hD.Zcent _ hz _ hw
    have hconj : x * ((l : G) * u * (l : G)⁻¹) * x⁻¹ = (l : G) * u * (l : G)⁻¹ := by
      have e1 : x * (l : G) * x⁻¹ = (x * (l : G) * x⁻¹ * (l : G)⁻¹) * l := by group
      have e2 : x * (u : G) * x⁻¹ = u := by rw [hxu]; group
      calc x * ((l : G) * u * (l : G)⁻¹) * x⁻¹
          = (x * (l : G) * x⁻¹) * (x * (u : G) * x⁻¹) * (x * (l : G) * x⁻¹)⁻¹ := by group
        _ = ((x * (l : G) * x⁻¹ * (l : G)⁻¹) * l) * u * ((x * (l : G) * x⁻¹ * (l : G)⁻¹) * l)⁻¹ := by
          rw [← e1, e2]
        _ = (x * (l : G) * x⁻¹ * (l : G)⁻¹) * ((l : G) * u * (l : G)⁻¹) *
            (x * (l : G) * x⁻¹ * (l : G)⁻¹)⁻¹ := by group
        _ = (l : G) * u * (l : G)⁻¹ := by rw [← hzc]; group
    have hcomm' : ((l : G) * u * (l : G)⁻¹) * x = x * ((l : G) * u * (l : G)⁻¹) := by
      have := hconj
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    refine NsQuot.mem_img.2 ⟨l * u * l⁻¹, Subgroup.mem_inf.2 ⟨hw, ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.2 hcomm'
    · rw [map_mul, map_mul, map_inv]
  have hsub : IsSubnormal (NsQuot.img N f J)
      (NsQuot.img N f L ⊓ Subgroup.centralizer ({f ⟨x, hx⟩} : Set Q)) :=
    ((hJ.2.1.comap N.subtype).map f).trans (IsSubnormal.step hCle hnorm (IsSubnormal.refl _))
  let fJ : ↥J →* Q := f.comp (Subgroup.inclusion hJN)
  have hrange : fJ.range = NsQuot.img N f J := by
    ext q
    simp only [MonoidHom.mem_range, NsQuot.mem_img]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨Subgroup.inclusion hJN u, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  have hker : fJ.rangeRestrict.ker ≤ Subgroup.center ↥J := by
    intro u hu
    have h1 : fJ u = 1 := congrArg Subtype.val hu
    have hZ : ((Subgroup.inclusion hJN u : ↥N) : G) ∈ Z := (hD.mem_ker_iff _).1 h1
    rw [Subgroup.mem_center_iff]
    intro v
    exact Subtype.ext (hD.Zcent _ hZ _ (hJL v.2))
  have hq : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hJ.2.2
  have hqr : CFSG.IsQuasisimple ↥fJ.range :=
    CFSG.LocalCores.isQuasisimple_of_surjective hq fJ.rangeRestrict
      fJ.rangeRestrict_surjective hker
  refine ⟨NsQuot.img N f J, ⟨(NsQuot.img_mono hJ.1).trans hCle, hsub,
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hrange) hqr)⟩, ?_⟩
  obtain ⟨e⟩ := CFSG.LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hq
    fJ.rangeRestrict fJ.rangeRestrict_surjective hker
  exact ⟨((e.trans (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hrange)
    (Subgroup.map_center_eq _)))).symm⟩

end CFSG.StandardType

end
