module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.GFuse
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.GCentB
public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.XAssembly

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG.RankThree.GF2n.Smith81

theorem mem_L_of_centralizes_z {G : Type} [Group G] [Finite G] {t : G} {Q L : Subgroup G}
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
    (hz : c * S.z = S.z * c) : c ∈ S.L := by
  classical
  let H : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let N : Subgroup ↥H := Q.subgroupOf H
  have hb_eq : S.b = (QuotientGroup.mk (⟨b, R.le_cen_L R.b_mem⟩ : ↥H) : ↥H ⧸ N) := by
    have hl : (QuotientGroup.mk (⟨b, R.le_cen_L R.b_mem⟩ : ↥H) : ↥H ⧸ N) ∈ S.L :=
      (hSL _).2 ⟨⟨b, R.b_mem⟩, rfl⟩
    have h1 : S.eL ⟨(QuotientGroup.mk (⟨b, R.le_cen_L R.b_mem⟩ : ↥H) : ↥H ⧸ N), hl⟩ =
        bStd := by
      rw [hSe ⟨b, R.b_mem⟩ hl, R.b_mark]
    have h2 : (⟨(QuotientGroup.mk (⟨b, R.le_cen_L R.b_mem⟩ : ↥H) : ↥H ⧸ N), hl⟩ : ↥S.L) =
        S.eL.symm bStd := by
      rw [← h1]
      simp
    exact (congrArg Subtype.val h2).symm
  have img_le : S.img (Sgrp ⊔ Jgrp) ≤ S.L := by
    intro x hx
    simp only [CubeSetting.img] at hx
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact (S.eL.symm a).2
  have hB : ∀ d : ↥H ⧸ N, d * S.z = S.z * d → d * S.b = S.b * d →
      d ∈ S.img (Sgrp ⊔ Jgrp) :=
    fun d hdz hdb => mem_img_of_centralizes_z_b (hN := hN) R S hSL hSe d hdz hdb
  have hbc : c * S.b * c⁻¹ ∈ S.L :=
    img_le (conj_b_mem_img_of_cubeSetting S hB hz)
  obtain ⟨l, hl⟩ := (hSL (c * S.b * c⁻¹)).1 hbc
  obtain ⟨c0, rfl⟩ := QuotientGroup.mk_surjective c
  let xH : ↥H := c0 * ⟨b, R.le_cen_L R.b_mem⟩ * c0⁻¹
  have hxH_mk : (QuotientGroup.mk xH : ↥H ⧸ N) =
      QuotientGroup.mk (⟨l, R.le_cen_L l.2⟩ : ↥H) := by
    simp only [xH, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← hb_eq]
    exact hl.symm
  have hq_mem : (xH : G)⁻¹ * (l : G) ∈ Q := by
    have h := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hxH_mk)
    simpa using h
  have hx : (xH : G) ∈ Q ⊔ L := by
    have hxl : (xH : G) = (l : G) * ((xH : G)⁻¹ * (l : G))⁻¹ := by group
    rw [hxl]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right l.2)
      (Subgroup.mem_sup_left (Q.inv_mem hq_mem))
  have hconj : IsConj b (xH : G) := by
    rw [isConj_iff]
    exact ⟨(c0 : G), rfl⟩
  obtain ⟨h, hh, hconjh⟩ := exists_conj_eq_of_isConj_mem_sup R hx hconj
  have hc0_t : (c0 : G) * t = t * (c0 : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp c0.2
  have hh_t : (h : G) * t = t * (h : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (sup_le R.le_cen_Q R.le_cen_L hh)
  have hht : ((h : G) * (c0 : G)) * t = t * ((h : G) * (c0 : G)) := by
    rw [mul_assoc, hc0_t, ← mul_assoc, hh_t, mul_assoc]
  have hbcomm : ((h : G) * (c0 : G)) * b = b * ((h : G) * (c0 : G)) := by
    have h1 : ((h : G) * (c0 : G)) * b * ((h : G) * (c0 : G))⁻¹ = b := by
      have hx' : (h : G) * ((c0 : G) * b * (c0 : G)⁻¹) * (h : G)⁻¹ = b := by
        change (h : G) * (xH : G) * (h : G)⁻¹ = b
        exact hconjh
      calc ((h : G) * (c0 : G)) * b * ((h : G) * (c0 : G))⁻¹
          = (h : G) * ((c0 : G) * b * (c0 : G)⁻¹) * (h : G)⁻¹ := by group
        _ = b := hx'
    calc ((h : G) * (c0 : G)) * b
        = (((h : G) * (c0 : G)) * b * ((h : G) * (c0 : G))⁻¹) * ((h : G) * (c0 : G)) := by
          group
      _ = b * ((h : G) * (c0 : G)) := by rw [h1]
  have hcen : ((h : G) * (c0 : G)) ∈ Q ⊔ L := R.cen_le _ hht hbcomm
  have hc0_mem : (c0 : G) ∈ Q ⊔ L := by
    have hc0_eq : (c0 : G) = (h : G)⁻¹ * ((h : G) * (c0 : G)) := by group
    rw [hc0_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hcen
  have hc0_sup : c0 ∈ Q.subgroupOf H ⊔ L.subgroupOf H := by
    rw [← Subgroup.subgroupOf_sup R.le_cen_Q R.le_cen_L]
    exact Subgroup.mem_subgroupOf.2 hc0_mem
  obtain ⟨qH, hqQH, lH, hlLH, hq_eqH⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := Q.subgroupOf H) (t := L.subgroupOf H)).mp hc0_sup
  have hlL : (lH : G) ∈ L := Subgroup.mem_subgroupOf.1 hlLH
  have hq_one : (QuotientGroup.mk qH : ↥H ⧸ N) = 1 :=
    (QuotientGroup.eq_one_iff qH).2 hqQH
  have hc_eq : (QuotientGroup.mk c0 : ↥H ⧸ N) =
      QuotientGroup.mk (⟨(lH : G), R.le_cen_L hlL⟩ : ↥H) := by
    rw [show c0 = qH * lH from hq_eqH.symm,
      show (⟨(lH : G), R.le_cen_L hlL⟩ : ↥H) = lH from Subtype.ext rfl]
    simp only [QuotientGroup.mk_mul]
    rw [hq_one, one_mul]
  rw [hc_eq]
  exact (hSL _).2 ⟨⟨(lH : G), hlL⟩, rfl⟩

end CFSG.StandardType.FF81.CentE6
