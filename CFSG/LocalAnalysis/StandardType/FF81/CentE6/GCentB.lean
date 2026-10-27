module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.GFuse
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.GQuotient
import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatJ

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open scoped Pointwise
open CFSG.RankThree.GF2n.Smith81

theorem mem_img_of_centralizes_z_b {G : Type} [Group G] [Finite G] {t : G} {Q L : Subgroup G}
    {eL : ↥L ≃* SL(6, ZMod 2)} {π : ↥Q →* Multiplicative (A5Cube.Cube (ZMod 2))} {b : G}
    (R : RadSetting t Q L eL π b)
    [hN : (Q.subgroupOf (Subgroup.centralizer ({t} : Set G))).Normal]
    (S : CubeSetting (↥(Subgroup.centralizer ({t} : Set G)) ⧸
        Q.subgroupOf (Subgroup.centralizer ({t} : Set G))))
    (hSL : ∀ x, x ∈ S.L ↔ ∃ l : ↥L, (QuotientGroup.mk (⟨(l : G), R.le_cen_L l.2⟩ :
        ↥(Subgroup.centralizer ({t} : Set G))) :
          ↥(Subgroup.centralizer ({t} : Set G)) ⧸
            Q.subgroupOf (Subgroup.centralizer ({t} : Set G))) = x)
    (hSe : ∀ (l : ↥L) (hl : (QuotientGroup.mk (⟨(l : G), R.le_cen_L l.2⟩ :
        ↥(Subgroup.centralizer ({t} : Set G))) :
          ↥(Subgroup.centralizer ({t} : Set G)) ⧸
            Q.subgroupOf (Subgroup.centralizer ({t} : Set G))) ∈ S.L),
        S.eL ⟨_, hl⟩ = eL l)
    (c : ↥(Subgroup.centralizer ({t} : Set G)) ⧸
        Q.subgroupOf (Subgroup.centralizer ({t} : Set G)))
    (hz : c * S.z = S.z * c) (hb : c * S.b = S.b * c) : c ∈ S.img (Sgrp ⊔ Jgrp) := by
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let QH : Subgroup H := Q.subgroupOf H
  obtain ⟨cH₀, hc₀⟩ := QuotientGroup.mk_surjective c
  let cH : H := cH₀
  have hc : (QuotientGroup.mk cH : H ⧸ QH) = c := hc₀
  let bH : H := ⟨b, R.le_cen_L R.b_mem⟩
  have hbS : S.b = (QuotientGroup.mk bH : H ⧸ QH) := by
    have hlb : (QuotientGroup.mk bH : H ⧸ QH) ∈ S.L :=
      (hSL _).mpr ⟨⟨b, R.b_mem⟩, rfl⟩
    have hsym : S.eL.symm bStd = (⟨(QuotientGroup.mk bH : H ⧸ QH), hlb⟩ : ↥S.L) := by
      apply S.eL.injective
      rw [MulEquiv.apply_symm_apply]
      exact (R.b_mark).symm.trans (hSe ⟨b, R.b_mem⟩ hlb).symm
    show (S.eL.symm bStd : H ⧸ QH) = (QuotientGroup.mk bH : H ⧸ QH)
    rw [hsym]
  have hb_eq : (QuotientGroup.mk (cH * bH * cH⁻¹) : H ⧸ QH) = QuotientGroup.mk bH := by
    have h : (QuotientGroup.mk (cH * bH) : H ⧸ QH) = QuotientGroup.mk (bH * cH) := by
      have h0 := hb
      rw [← hc, hbS] at h0
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at h0
      exact h0
    calc (QuotientGroup.mk (cH * bH * cH⁻¹) : H ⧸ QH)
        = QuotientGroup.mk (cH * bH) * QuotientGroup.mk cH⁻¹ := by
            rw [show cH * bH * cH⁻¹ = (cH * bH) * cH⁻¹ from by group]
            rfl
      _ = QuotientGroup.mk (bH * cH) * QuotientGroup.mk cH⁻¹ := by rw [h]
      _ = QuotientGroup.mk ((bH * cH) * cH⁻¹) := rfl
      _ = QuotientGroup.mk bH := by
            rw [show (bH * cH) * cH⁻¹ = bH from by group]
  have hxQ : ((cH : G) * b * (cH : G)⁻¹) * b⁻¹ ∈ Q := by
    have h := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq_iff_div_mem.mp hb_eq)
    simpa [bH, Subgroup.coe_div, Subgroup.coe_mul, Subgroup.coe_inv, div_eq_mul_inv] using h
  have hx_sup : (cH : G) * b * (cH : G)⁻¹ ∈ Q ⊔ L := by
    have h := Subgroup.mul_mem_sup hxQ R.b_mem
    have heq : (((cH : G) * b * (cH : G)⁻¹) * b⁻¹) * b =
        (cH : G) * b * (cH : G)⁻¹ := by group
    rwa [heq] at h
  have hconj : IsConj b ((cH : G) * b * (cH : G)⁻¹) :=
    isConj_iff.mpr ⟨(cH : G), rfl⟩
  obtain ⟨h, hh_sup, hhx⟩ := exists_conj_eq_of_isConj_mem_sup R hx_sup hconj
  have hhH : h ∈ H := (sup_le R.le_cen_Q R.le_cen_L) hh_sup
  have hht : h * t = t * h := Subgroup.mem_centralizer_singleton_iff.mp hhH
  have hct : (cH : G) * t = t * (cH : G) := Subgroup.mem_centralizer_singleton_iff.mp cH.2
  have hgt : (h * (cH : G)) * t = t * (h * (cH : G)) := by
    calc (h * (cH : G)) * t = h * ((cH : G) * t) := by rw [mul_assoc]
      _ = h * (t * (cH : G)) := by rw [hct]
      _ = (h * t) * (cH : G) := by rw [mul_assoc]
      _ = (t * h) * (cH : G) := by rw [hht]
      _ = t * (h * (cH : G)) := by rw [mul_assoc]
  have hhx' : h * ((cH : G) * b * (cH : G)⁻¹) = b * h :=
    mul_inv_eq_iff_eq_mul.mp hhx
  have hxb : (cH : G) * b = ((cH : G) * b * (cH : G)⁻¹) * (cH : G) := by group
  have hgb : (h * (cH : G)) * b = b * (h * (cH : G)) := by
    calc (h * (cH : G)) * b = h * ((cH : G) * b) := by rw [mul_assoc]
      _ = h * (((cH : G) * b * (cH : G)⁻¹) * (cH : G)) :=
            congrArg (fun z => h * z) hxb
      _ = (h * ((cH : G) * b * (cH : G)⁻¹)) * (cH : G) := by rw [← mul_assoc]
      _ = (b * h) * (cH : G) := by rw [hhx']
      _ = b * (h * (cH : G)) := by rw [mul_assoc]
  have hg_sup : h * (cH : G) ∈ Q ⊔ L := R.cen_le (h * (cH : G)) hgt hgb
  have hcG_sup : (cH : G) ∈ Q ⊔ L := by
    have h1 : h⁻¹ * (h * (cH : G)) = (cH : G) := by group
    rw [← h1]
    exact Subgroup.mul_mem (Q ⊔ L) (Subgroup.inv_mem (Q ⊔ L) hh_sup) hg_sup
  have hnorm : L ≤ Subgroup.normalizer Q := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      exact R.conj_mem l hl q hq
    · intro hq
      have h2 := R.conj_mem l⁻¹ (L.inv_mem hl) (l * q * l⁻¹) hq
      rwa [show l⁻¹ * (l * q * l⁻¹) * (l⁻¹)⁻¹ = q from by group] at h2
  have hcoe : (↑(Q ⊔ L) : Set G) = (Q : Set G) * (L : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q L hnorm
  have hcG_mul : (cH : G) ∈ (Q : Set G) * (L : Set G) := by
    rw [← hcoe]
    exact hcG_sup
  rw [Set.mem_mul] at hcG_mul
  obtain ⟨q, hqQ, l, hlL, hql⟩ := hcG_mul
  have hqH : q ∈ H := R.le_cen_Q hqQ
  have hlH : l ∈ H := R.le_cen_L hlL
  have hqQH : (⟨q, hqH⟩ : H) ∈ QH := Subgroup.mem_subgroupOf.mpr hqQ
  have hql' : (⟨q, hqH⟩ : H) * (⟨l, hlH⟩ : H) = cH := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact hql
  have hc_eq : c = (QuotientGroup.mk (⟨l, hlH⟩ : H) : H ⧸ QH) := by
    rw [← hc, ← hql', QuotientGroup.mk_mul]
    have hq_one : (QuotientGroup.mk (⟨q, hqH⟩ : H) : H ⧸ QH) = 1 :=
      (QuotientGroup.eq_one_iff (N := QH) (⟨q, hqH⟩ : H)).mpr hqQH
    rw [hq_one, one_mul]
  have hl : (QuotientGroup.mk (⟨l, hlH⟩ : H) : H ⧸ QH) ∈ S.L :=
    (hSL _).mpr ⟨⟨l, hlL⟩, rfl⟩
  let a : SL(6, ZMod 2) := eL ⟨l, hlL⟩
  have hsym_a : S.eL.symm a =
      (⟨(QuotientGroup.mk (⟨l, hlH⟩ : H) : H ⧸ QH), hl⟩ : ↥S.L) := by
    apply S.eL.injective
    rw [MulEquiv.apply_symm_apply]
    exact (hSe ⟨l, hlL⟩ hl).symm
  have h1 : (S.eL.symm a : H ⧸ QH) = c := by
    rw [hsym_a]
    exact hc_eq.symm
  have hSz : S.z = (S.eL.symm CFSG.Holt.SL6.stdTransvection : H ⧸ QH) := rfl
  have hz1 : (S.eL.symm a : H ⧸ QH) *
        (S.eL.symm CFSG.Holt.SL6.stdTransvection : H ⧸ QH) =
      (S.eL.symm CFSG.Holt.SL6.stdTransvection : H ⧸ QH) *
        (S.eL.symm a : H ⧸ QH) := by
    rw [h1, ← hSz]
    exact hz
  have hzSL : S.eL.symm a * S.eL.symm CFSG.Holt.SL6.stdTransvection =
      S.eL.symm CFSG.Holt.SL6.stdTransvection * S.eL.symm a := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hz1
  have hcomm : a * CFSG.Holt.SL6.stdTransvection =
      CFSG.Holt.SL6.stdTransvection * a := by
    have h := congrArg S.eL hzSL
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  have ha_cen : a ∈ Subgroup.centralizer
      ({CFSG.Holt.SL6.stdTransvection} : Set SL(6, ZMod 2)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have ha_sup : a ∈ Sgrp ⊔ Jgrp := by
    rw [← centralizer_stdTransvection_eq]
    exact ha_cen
  exact Subgroup.mem_map.mpr ⟨a, ha_sup, h1⟩

end CFSG.StandardType.FF81.CentE6
