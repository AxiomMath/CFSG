module

public import CFSG.RankThree.PartTwo.Sec16.Item163P6Conf
public import CFSG.RankThree.PartTwo.Sec16.Item163P6Act
public import CFSG.RankThree.PartTwo.KFacts.KS163P6
import CFSG.RankThree.PartTwo.Sec16.Item163P6Shape
import CFSG.GroupTheory.InnerNormalizedAutomorphisms
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163P6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section ActL

variable {Y L : Subgroup G} (hLY : L ≤ Y)
  (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y)
  (hL : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥)

theorem actL_apply_of_conj_mem (g : Subgroup.normalizer (Y : Set G)) {l : G} (hl : l ∈ L)
    (hgl : (g : G) * l * (g : G)⁻¹ ∈ L) :
    actL hLY hY hL g ⟨l, hl⟩ = ⟨(g : G) * l * (g : G)⁻¹, hgl⟩ := by
  apply (quotEquiv hLY hY hL).injective
  have h1 : (quotEquiv hLY hY hL) (actL hLY hY hL g ⟨l, hl⟩) =
      actQ Y g ((quotEquiv hLY hY hL) ⟨l, hl⟩) := by
    change (quotEquiv hLY hY hL)
        ((MulAut.congr (quotEquiv hLY hY hL).symm) (actQ Y g) ⟨l, hl⟩) =
      actQ Y g ((quotEquiv hLY hY hL) ⟨l, hl⟩)
    rw [MulAut.congr_apply]
    simp
  rw [h1, quotEquiv_apply, actQ_mk, quotEquiv_apply]
  have h2 : Y.normalizerMonoidHom g (Subgroup.inclusion hLY ⟨l, hl⟩) =
      Subgroup.inclusion hLY ⟨(g : G) * l * (g : G)⁻¹, hgl⟩ := by
    apply Subtype.ext
    rfl
  rw [h2]

theorem actL_mem_centralizer {D : Subgroup G} (hDL : D ≤ L)
    (g : Subgroup.normalizer (Y : Set G))
    (hg : (g : G) ∈ Subgroup.centralizer (D : Set G)) :
    actL hLY hY hL g ∈ Subgroup.centralizer
      (((D.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) : Subgroup (MulAut ↥L)) :
        Set (MulAut ↥L)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
  have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
  have hdL : (d : G) ∈ L := hDL hdD
  have hcomm : (d : G) * (g : G) = (g : G) * (d : G) :=
    Subgroup.mem_centralizer_iff.mp hg (d : G) hdD
  have hfix : actL hLY hY hL g d = d := by
    have hgl : (g : G) * (d : G) * (g : G)⁻¹ ∈ L := by
      rw [show (g : G) * (d : G) * (g : G)⁻¹ = (d : G) by
        calc (g : G) * (d : G) * (g : G)⁻¹ = (d : G) * (g : G) * (g : G)⁻¹ := by
              rw [hcomm]
          _ = (d : G) := by group]
      exact hdL
    change actL hLY hY hL g (⟨(d : G), hdL⟩ : ↥L) = d
    rw [actL_apply_of_conj_mem hLY hY hL g hdL hgl]
    apply Subtype.ext
    change (g : G) * (d : G) * (g : G)⁻¹ = (d : G)
    rw [← hcomm]
    group
  have hmul : actL hLY hY hL g * MulAut.conj d =
      MulAut.conj d * actL hLY hY hL g := by
    have h := CFSG.InnerNormalizedAutomorphisms.mul_conj_mul_inv_eq
      (actL hLY hY hL g) d
    rw [hfix] at h
    calc actL hLY hY hL g * MulAut.conj d
        = (actL hLY hY hL g * MulAut.conj d * (actL hLY hY hL g)⁻¹) *
            actL hLY hY hL g := by group
      _ = MulAut.conj d * actL hLY hY hL g := by rw [h]
  exact hmul.symm

private theorem map_conj_subgroupOf_le_map_actL {D R : Subgroup G} (hDL : D ≤ L)
    (hDR : D ≤ R) :
    (D.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) ≤
      (R.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actL hLY hY hL) := by
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
  have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
  have hdL : (d : G) ∈ L := hDL hdD
  have hdR : (d : G) ∈ R := hDR hdD
  have hdN : (d : G) ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer (hLY hdL)
  refine Subgroup.mem_map.mpr
    ⟨⟨(d : G), hdN⟩, Subgroup.mem_subgroupOf.mpr hdR, ?_⟩
  have hd_eq : (⟨(d : G), hdL⟩ : ↥L) = d := Subtype.ext rfl
  simpa [hd_eq] using actL_of_mem hLY hY hL hdL

private theorem map_actL_le_map_conj_sup_centralizer {D R : Subgroup G} (hDL : D ≤ L)
    (hRC : R ≤ D ⊔ Subgroup.centralizer (D : Set G)) :
    (R.subgroupOf (Subgroup.normalizer (Y : Set G))).map (actL hLY hY hL) ≤
      (D.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) ⊔
        Subgroup.centralizer (((D.subgroupOf L).map
          (MulAut.conj : ↥L →* MulAut ↥L) : Subgroup (MulAut ↥L)) : Set (MulAut ↥L)) := by
  let N : Subgroup G := Subgroup.normalizer (Y : Set G)
  intro t ht
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ht
  have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
  have hrDsup : (r : G) ∈ D ⊔ Subgroup.centralizer (D : Set G) := hRC hrR
  have hDnorm : D ≤ Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) :=
    D.le_normalizer.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer D)
  have hrDsup' : (r : G) ∈ (D : Set G) * (Subgroup.centralizer (D : Set G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right D
      (Subgroup.centralizer (D : Set G)) hDnorm]
    exact hrDsup
  obtain ⟨d, hdD, z, hzC, hdz⟩ := hrDsup'
  have hdL : d ∈ L := hDL hdD
  have hdN : d ∈ N := Subgroup.le_normalizer (hLY hdL)
  have hzN : z ∈ N := by
    have hz_eq : z = d⁻¹ * (r : G) := by rw [← hdz]; group
    rw [hz_eq]
    exact N.mul_mem (N.inv_mem hdN) r.2
  let dN : N := ⟨d, hdN⟩
  let zN : N := ⟨z, hzN⟩
  have hr_eq : r = dN * zN := by
    apply Subtype.ext
    simpa using hdz.symm
  rw [hr_eq, map_mul]
  refine Subgroup.mul_mem_sup ?_ ?_
  · refine Subgroup.mem_map.mpr
      ⟨⟨d, hdL⟩, Subgroup.mem_subgroupOf.mpr hdD, ?_⟩
    exact (actL_of_mem hLY hY hL hdL).symm
  · exact actL_mem_centralizer hLY hY hL hDL zN hzC

private theorem map_conj_le_normalizer_map_actL {E R : Subgroup G} (hEL : E ≤ L)
    (hER : E ≤ Subgroup.normalizer (R : Set G)) :
    (E.subgroupOf L).map (MulAut.conj : ↥L →* MulAut ↥L) ≤
      Subgroup.normalizer (((R.subgroupOf (Subgroup.normalizer (Y : Set G))).map
        (actL hLY hY hL) : Subgroup (MulAut ↥L)) : Set (MulAut ↥L)) := by
  let N : Subgroup G := Subgroup.normalizer (Y : Set G)
  let T : Subgroup (MulAut ↥L) := (R.subgroupOf N).map (actL hLY hY hL)
  have hmap_le : ∀ e ∈ E.subgroupOf L, ∀ t ∈ T,
      MulAut.conj e * t * (MulAut.conj e)⁻¹ ∈ T := by
    intro e he t ht
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ht
    have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
    have heL : (e : G) ∈ L := hEL heE
    have heNR : (e : G) ∈ Subgroup.normalizer (R : Set G) := hER heE
    have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    have hconjR : (e : G) * (r : G) * (e : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp heNR (r : G)).mp hrR
    have heN : (e : G) ∈ N := Subgroup.le_normalizer (hLY heL)
    have hconjN : (e : G) * (r : G) * (e : G)⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem heN r.2) (N.inv_mem heN)
    refine Subgroup.mem_map.mpr
      ⟨⟨(e : G) * (r : G) * (e : G)⁻¹, hconjN⟩,
        Subgroup.mem_subgroupOf.mpr hconjR, ?_⟩
    have hEq : (⟨(e : G) * (r : G) * (e : G)⁻¹, hconjN⟩ : N) =
        ⟨(e : G), heN⟩ * r * (⟨(e : G), heN⟩)⁻¹ := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [hEq, map_mul, map_mul, map_inv, actL_of_mem hLY hY hL heL]
  intro x hx
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    change MulAut.conj (MulAut.conj e) t ∈ T
    rw [MulAut.conj_apply]
    exact hmap_le e he t ht
  · intro t ht
    have hmem : (MulAut.conj e)⁻¹ * t * (MulAut.conj e) ∈ T := by
      simpa [map_inv] using hmap_le e⁻¹ ((E.subgroupOf L).inv_mem he) t ht
    refine Subgroup.mem_map.mpr ⟨(MulAut.conj e)⁻¹ * t * (MulAut.conj e), hmem, ?_⟩
    change MulAut.conj (MulAut.conj e)
      ((MulAut.conj e)⁻¹ * t * MulAut.conj e) = t
    rw [MulAut.conj_apply]
    group

end ActL

namespace Conf685

variable {A : Subgroup G} {c : G} {L Y S : Subgroup G}

theorem exists_actQ_eq_one_of_eq_sup
    (h : Conf685 A c L Y S)
    (hC : KFacts.KS163P6Cent) {Y' R : Subgroup G} (hY' : Y' ∈ scriptY0Star A (lB A))
    (hR : R ∈ scriptQPi A (lB A) ⊤ (piOf 2)) (hRY : R ≤ Subgroup.normalizer (Y' : Set G))
    (hDR : S ⊓ L < R)
    (hRC : R ≤ (S ⊓ L) ⊔ Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G))
    (hY : Y' = L ⊔ CFSG.Open.pCoreOf 2 Y') :
    ∃ r ∈ R, r ≠ 1 ∧ ∃ hr : r ∈ Subgroup.normalizer (Y' : Set G),
      actQ Y' ⟨r, hr⟩ = 1 := by
  classical
  have hLY : L ≤ Y' := h.le_y Y' hY'
  have hL : L ⊓ CFSG.Open.pCoreOf 2 Y' = ⊥ := inf_pCoreOf_eq_bot h hY'
  let D : Subgroup G := S ⊓ L
  let E : Subgroup G := A ⊓ L
  let D' : Subgroup ↥L := D.subgroupOf L
  let E' : Subgroup ↥L := E.subgroupOf L
  let N : Subgroup G := Subgroup.normalizer (Y' : Set G)
  let ψ : N →* MulAut ↥L := actL hLY hY hL
  let T : Subgroup (MulAut ↥L) := (R.subgroupOf N).map ψ
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hR.2
  have hT2 : IsPGroup 2 T := (hR2.comap_subtype (K := N)).map ψ
  have hDT : D'.map (MulAut.conj : ↥L →* MulAut ↥L) ≤ T :=
    map_conj_subgroupOf_le_map_actL hLY hY hL (D := D) (R := R)
      inf_le_right hDR.le
  have hTC : T ≤ D'.map (MulAut.conj : ↥L →* MulAut ↥L) ⊔
      Subgroup.centralizer (((D'.map (MulAut.conj : ↥L →* MulAut ↥L) :
        Subgroup (MulAut ↥L)) : Set (MulAut ↥L))) :=
    map_actL_le_map_conj_sup_centralizer hLY hY hL (D := D) (R := R)
      inf_le_right hRC
  have hER : E ≤ Subgroup.normalizer (R : Set G) := by
    intro e he
    exact (mem_scriptQ_iff.mp hR.1.1).2.1 ((show E ≤ A from inf_le_left) he)
  have hET : E'.map (MulAut.conj : ↥L →* MulAut ↥L) ≤
      Subgroup.normalizer (T : Set (MulAut ↥L)) :=
    map_conj_le_normalizer_map_actL hLY hY hL (E := E) (R := R)
      inf_le_right hER
  have hT_eq : T = D'.map (MulAut.conj : ↥L →* MulAut ↥L) :=
    hC ↥L (isType163P6 h) E' (isElemAbelian_inf h) (card_inf_subgroupOf h)
      D' (isMaxInvTwo h) T hT2 hDT hTC hET
  obtain ⟨r, hrR, hrD⟩ := SetLike.exists_of_lt hDR
  have hrN : r ∈ N := hRY hrR
  have hψr_mem : ψ ⟨r, hrN⟩ ∈ T := by
    exact Subgroup.mem_map.mpr
      ⟨⟨r, hrN⟩, Subgroup.mem_subgroupOf.mpr hrR, rfl⟩
  rw [hT_eq] at hψr_mem
  obtain ⟨d, hd, hψr_eq⟩ := Subgroup.mem_map.mp hψr_mem
  have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
  have hdL : (d : G) ∈ L := (show D ≤ L from inf_le_right) hdD
  let dN : N := ⟨(d : G), Subgroup.le_normalizer (hLY hdL)⟩
  have hd_eq : (⟨(d : G), hdL⟩ : ↥L) = d := Subtype.ext rfl
  have hψd : ψ dN = MulAut.conj d := by
    simpa [hd_eq] using actL_of_mem hLY hY hL hdL
  have hψd_eq : ψ dN = ψ ⟨r, hrN⟩ := hψd.trans hψr_eq
  have hr'R : r * (d : G)⁻¹ ∈ R :=
    R.mul_mem hrR (R.inv_mem (hDR.le hdD))
  have hr'1 : r * (d : G)⁻¹ ≠ 1 := by
    intro h1
    have hrd : r = (d : G) := mul_inv_eq_one.mp h1
    rw [← hrd] at hdD
    exact hrD hdD
  have hr'N : r * (d : G)⁻¹ ∈ N := N.mul_mem hrN (N.inv_mem dN.2)
  have hψr' : ψ ⟨r * (d : G)⁻¹, hr'N⟩ = 1 := by
    have hr_eq_N : (⟨r * (d : G)⁻¹, hr'N⟩ : N) = ⟨r, hrN⟩ * dN⁻¹ := by
      apply Subtype.ext
      rfl
    rw [hr_eq_N, map_mul, map_inv, hψd_eq, mul_inv_cancel]
  exact ⟨r * (d : G)⁻¹, hr'R, hr'1, hr'N,
    (actL_eq_one_iff hLY hY hL ⟨r * (d : G)⁻¹, hr'N⟩).mp hψr'⟩

end Conf685

end CFSG.RankThree.PartTwo.Sec16.Proof163P6

end
