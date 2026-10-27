module

public import CFSG.LocalAnalysis.WeakClosure81.W16PLemmaQA
public import CFSG.LocalAnalysis.WeakClosure81.W16POneMod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg161

variable {M V₀ V U : Subgroup G} {g : G}

private theorem not_le_pCoreOf (h152 : Thm152 G) (c : Cfg161 M V₀ V U g)
    (hV : V ≤ V₀ ⊔ (V ⊓ centralizer (conjSubgroup V g : Set G))) :
    ¬ V₀ ≤ pCoreOf 2 (conjSubgroup M g) := by
  let H := conjSubgroup M g
  let A := conjSubgroup V g
  have hVH : V ≤ H := le_conjSubgroup h152 c
  have hV0H : V₀ ≤ H := c.hyp.h6.le.trans hVH
  have hAab : IsElemAbelian 2 A := by
    simpa [A, conjSubgroup] using
      c.hyp.h6.elemAbelian.map (MulAut.conj g⁻¹).toMonoidHom
  have hHN : H ≤ Subgroup.normalizer (A : Set G) := by
    calc H = conjSubgroup M g := rfl
      _ ≤ conjSubgroup (Subgroup.normalizer (V : Set G)) g :=
          E3.conjSubgroup_mono_left g (le_of_eq c.hyp.h6.normalizer_eq.symm)
      _ = Subgroup.normalizer (conjSubgroup V g : Set G) := conjSubgroup_normalizer V g
      _ = Subgroup.normalizer (A : Set G) := rfl
  obtain ⟨D⟩ := exists_modDataE (J := H) (E := A) hAab hHN
  intro hle
  have hPle : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hImgLe : D.img V₀ ≤ pCoreOf 2 (D.img H) := by
    refine (D.img_mono hle).trans ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (D.img_mono hPle)
      (D.img_le_normalizer (S := pCoreOf 2 H) le_rfl hPle
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (D.isPGroup_img (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H))
  have hbot : D.img V₀ = ⊥ := by
    have hleinf : D.img V₀ ≤ D.img V ⊓ pCoreOf 2 (D.img H) :=
      le_inf (D.img_mono c.hyp.h6.le) hImgLe
    rw [inf_pCoreOf_img h152 c D] at hleinf
    exact le_bot_iff.1 hleinf
  have hcent : V₀ ≤ centralizer (A : Set G) :=
    D.le_centralizer_of_img_eq_bot hV0H hbot
  apply c.not_comm
  intro x hx y hy
  have hV0le : V₀ ≤ Subgroup.centralizer ({y} : Set G) := by
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 (hcent hv) y hy).symm)
  have hCle : V ⊓ centralizer (A : Set G) ≤ Subgroup.centralizer ({y} : Set G) := by
    intro cc hcc
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((Subgroup.mem_centralizer_iff.1 hcc.2 y hy).symm)
  exact Subgroup.mem_centralizer_singleton_iff.1 (hV.trans (sup_le hV0le hCle) hx)

private theorem exists_not_isPGroup (h152 : Thm152 G) (c : Cfg161 M V₀ V U g)
    (hV : V ≤ V₀ ⊔ (V ⊓ centralizer (conjSubgroup V g : Set G))) :
    ∃ h ∈ conjSubgroup M g, ¬ IsPGroup 2 ↥(V₀ ⊔ conjSubgroup V₀ h) := by
  let H := conjSubgroup M g
  have hV0H : V₀ ≤ H := c.hyp.h6.le.trans (le_conjSubgroup h152 c)
  have hX2 : IsPGroup 2 (V₀.subgroupOf H) :=
    (CFSG.Open.IsElemAbelian.isPGroup c.hyp.elemAbelian₀).of_equiv
      (Subgroup.subgroupOfEquivOfLe hV0H).symm
  rcases baer_suzuki_subgroup (G := ↥H) (p := 2) (X := V₀.subgroupOf H) hX2 with hle | ⟨h', hh'⟩
  · exfalso
    apply not_le_pCoreOf h152 c hV
    intro v hv
    exact ⟨⟨v, hV0H hv⟩,
      hle (show (⟨v, hV0H hv⟩ : ↥H) ∈ V₀.subgroupOf H from hv), rfl⟩
  · have hV0gH : conjSubgroup V₀ (h' : G) ≤ H := by
      intro y hy
      rw [mem_conjSubgroup_iff] at hy
      have e : y = (h' : G)⁻¹ * ((h' : G) * y * (h' : G)⁻¹) * (h' : G) := by group
      rw [e]
      exact H.mul_mem (H.mul_mem (H.inv_mem h'.2) (hV0H hy)) h'.2
    have hmap : (V₀.subgroupOf H ⊔ conjSubgroup (V₀.subgroupOf H) h').map H.subtype =
        V₀ ⊔ conjSubgroup V₀ (h' : G) := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hV0H]
      congr 1
      ext y
      constructor
      · intro hy
        rw [Subgroup.mem_map] at hy
        obtain ⟨y', hy', rfl⟩ := hy
        rw [mem_conjSubgroup_iff] at hy' ⊢
        simpa using Subgroup.mem_subgroupOf.mp hy'
      · intro hy
        rw [mem_conjSubgroup_iff] at hy
        refine Subgroup.mem_map.2 ⟨⟨y, ?_⟩, ?_, rfl⟩
        · have : y = (h' : G)⁻¹ * ((h' : G) * y * (h' : G)⁻¹) * (h' : G) := by group
          rw [this]
          exact H.mul_mem (H.mul_mem (H.inv_mem h'.2) (hV0H hy)) h'.2
        · rw [mem_conjSubgroup_iff]
          exact Subgroup.mem_subgroupOf.mpr hy
    refine ⟨(h' : G), h'.2, ?_⟩
    intro hpg
    apply hh'
    have h2Y : IsPGroup 2 ↥((V₀.subgroupOf H ⊔
        conjSubgroup (V₀.subgroupOf H) h').map H.subtype) := hmap ▸ hpg
    exact h2Y.of_equiv ((V₀.subgroupOf H ⊔ conjSubgroup (V₀.subgroupOf H) h').equivMapOfInjective
      H.subtype H.subtype_injective).symm

theorem exists_cfgLemmaQ (h152 : Thm152 G) (c : Cfg161 M V₀ V U g)
    (hV : V ≤ V₀ ⊔ (V ⊓ centralizer (conjSubgroup V g : Set G))) :
    ∃ h ∈ conjSubgroup M g, CfgLemmaQ M V₀ V h (V ⊓ centralizer (conjSubgroup V g : Set G)) := by
  let A := conjSubgroup V g
  let C := V ⊓ centralizer (A : Set G)
  obtain ⟨h, hhH, hnotX⟩ := exists_not_isPGroup h152 c hV
  have hVH : V ≤ conjSubgroup M g := le_conjSubgroup h152 c
  have hAH : A ≤ conjSubgroup M g := E3.conjSubgroup_mono_left g c.hyp.h6.le_M
  have hAab : IsElemAbelian 2 A := by
    simpa [A, conjSubgroup] using
      c.hyp.h6.elemAbelian.map (MulAut.conj g⁻¹).toMonoidHom
  have hHN : conjSubgroup M g ≤ Subgroup.normalizer (A : Set G) := by
    calc conjSubgroup M g ≤ conjSubgroup (Subgroup.normalizer (V : Set G)) g :=
          E3.conjSubgroup_mono_left g (le_of_eq c.hyp.h6.normalizer_eq.symm)
      _ = Subgroup.normalizer (conjSubgroup V g : Set G) := conjSubgroup_normalizer V g
      _ = Subgroup.normalizer (A : Set G) := rfl
  have hAeq : conjSubgroup A h = A :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hHN hhH)
  have hNormH : Subgroup.normalizer (conjSubgroup V₀ h : Set G) = conjSubgroup M h := by
    rw [← conjSubgroup_normalizer V₀ h, c.hyp.normalizer₀]
  have hTIh : CFSG.CGT.Timmesfeld75.IsTI (conjSubgroup V₀ h) := by
    simpa [CFSG.Quasithin.conjSubgroup, CFSG.CGT.Timmesfeld75.conjSubgroup] using
      CFSG.RankThree.GF2n.isTI_conjSubgroup c.hyp.isTI h⁻¹
  have hZ0ne : V₀ ⊓ A ≠ ⊥ := inf_ne_bot h152 c
  have hZ0h_ne : conjSubgroup (V₀ ⊓ A) h ≠ ⊥ := by
    intro hbot
    have h1 : conjSubgroup (conjSubgroup (V₀ ⊓ A) h) h⁻¹ = (⊥ : Subgroup G) := by
      rw [hbot]
      exact Subgroup.map_bot _
    have h2 : conjSubgroup (conjSubgroup (V₀ ⊓ A) h) h⁻¹ = V₀ ⊓ A := by
      rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    rw [h2] at h1
    exact hZ0ne h1
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ0h_ne
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hzV0h : z ∈ conjSubgroup V₀ h :=
    (E3.conjSubgroup_mono_left h inf_le_left) hz
  have hzA : z ∈ A := by
    have hz' : z ∈ conjSubgroup A h := (E3.conjSubgroup_mono_left h inf_le_right) hz
    rwa [hAeq] at hz'
  have hleMh : V₀ ⊓ A ≤ conjSubgroup M h := by
    intro x hx
    have hxA : x ∈ A := hx.2
    have hcomm : x * z = z * x :=
      congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hxA⟩ ⟨z, hzA⟩)
    have hxCent : x ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hcomm
    have hx := centralizer_le_normalizer_of_isTI hTIh hzV0h hz1' hxCent
    rwa [hNormH] at hx
  have hle_conj : C ≤ conjSubgroup M h := by
    intro cc hcc
    have hccCent : cc ∈ centralizer (A : Set G) := hcc.2
    have hcomm : cc * z = z * cc :=
      (Subgroup.mem_centralizer_iff.1 hccCent z hzA).symm
    have hccCentZ : cc ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hcomm
    have hcc := centralizer_le_normalizer_of_isTI hTIh hzV0h hz1' hccCentZ
    rwa [hNormH] at hcc
  have hnotLe : ¬ V ≤ conjSubgroup M h := by
    intro hle
    apply hnotX
    have hV2 : IsPGroup 2 V := c.hyp.isPGroup
    have hVh2 : IsPGroup 2 (conjSubgroup V h) := E3.isPGroup_conjSubgroup hV2 h
    have hnorm : V ≤ Subgroup.normalizer (conjSubgroup V h : Set G) := by
      rw [← conjSubgroup_normalizer, c.hyp.h6.normalizer_eq]
      exact hle
    have hsup2 : IsPGroup 2 (V ⊔ conjSubgroup V h : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hV2 hVh2 hnorm
    refine hsup2.to_le (sup_le ?_ ?_)
    · exact c.hyp.h6.le.trans le_sup_left
    · exact (E3.conjSubgroup_mono_left h c.hyp.h6.le).trans le_sup_right
  have hdisj : V ⊓ conjSubgroup V₀ h = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    by_contra hw1
    apply hnotLe
    have hVab : IsElemAbelian 2 V := c.hyp.h6.elemAbelian
    have hVsub : V ≤ Subgroup.centralizer ({w} : Set G) := by
      intro v hv
      have hcomm : v * w = w * v :=
        congrArg Subtype.val (hVab.1.is_comm.comm ⟨v, hv⟩ ⟨w, hw.1⟩)
      exact Subgroup.mem_centralizer_singleton_iff.2 hcomm
    have hCw : Subgroup.centralizer ({w} : Set G) ≤ conjSubgroup M h := by
      have hw := centralizer_le_normalizer_of_isTI hTIh hw.2 hw1
      rwa [hNormH] at hw
    exact hVsub.trans hCw
  have hle_centralizer :
      C ≤ centralizer ((conjSubgroup V₀ h ⊓ M : Subgroup G) : Set G) := by
    intro cc hcc
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbV0h : b ∈ conjSubgroup V₀ h := hb.1
    have hbM : b ∈ M := hb.2
    have hccV : cc ∈ V := hcc.1
    have hccMh : cc ∈ conjSubgroup M h := hle_conj hcc
    have hbN : b ∈ Subgroup.normalizer (V : Set G) := by
      rw [c.hyp.h6.normalizer_eq]
      exact hbM
    have hbcV : b * cc * b⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 hbN cc).1 hccV
    have hcommV : b * cc * b⁻¹ * cc⁻¹ ∈ V := V.mul_mem hbcV (V.inv_mem hccV)
    have hccN : cc ∈ Subgroup.normalizer (conjSubgroup V₀ h : Set G) := by
      rw [hNormH]
      exact hccMh
    have hcbc : cc * b⁻¹ * cc⁻¹ ∈ conjSubgroup V₀ h :=
      (Subgroup.mem_normalizer_iff.1 hccN b⁻¹).1
        ((conjSubgroup V₀ h).inv_mem hbV0h)
    have hcommW : b * (cc * b⁻¹ * cc⁻¹) ∈ conjSubgroup V₀ h :=
      (conjSubgroup V₀ h).mul_mem hbV0h hcbc
    have heq : b * cc * b⁻¹ * cc⁻¹ = b * (cc * b⁻¹ * cc⁻¹) := by group
    have hmem : b * cc * b⁻¹ * cc⁻¹ ∈ (⊥ : Subgroup G) := by
      rw [← hdisj]
      exact ⟨hcommV, heq ▸ hcommW⟩
    have h1 : b * cc * b⁻¹ * cc⁻¹ = 1 := Subgroup.mem_bot.1 hmem
    have h2 : b * cc * b⁻¹ = cc := mul_inv_eq_one.mp h1
    calc b * cc = (b * cc * b⁻¹) * b := by group
      _ = cc * b := by rw [h2]
  refine ⟨h, hhH, ?_⟩
  refine ⟨c.hyp, hnotX, ?_, inf_le_left, ?_, hle_conj, hle_centralizer⟩
  · intro hbot
    apply hZ0ne
    rw [eq_bot_iff]
    intro x hx
    have hxMh : x ∈ conjSubgroup M h := hleMh hx
    have hx' : x ∈ V₀ ⊓ conjSubgroup M h := ⟨hx.1, hxMh⟩
    rw [hbot] at hx'
    exact hx'
  · rwa [sup_comm]

end Cfg161

end CFSG.LocalAnalysis.WeakClosure81

end
