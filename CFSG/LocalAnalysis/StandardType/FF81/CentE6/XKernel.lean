module

public import CFSG.LocalAnalysis.StandardType.FF81.CentE6.CubeW
import CFSG.LocalAnalysis.StandardType.FF81.CentE6.MatD
import CFSG.LocalAnalysis.StandardType.FS81.S7SelfNormL3Two

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups

private abbrev markHom {X : Type} [Group X] (S : CubeSetting X) : SL(6, ZMod 2) →* X :=
  S.L.subtype.comp S.eL.symm.toMonoidHom

private theorem img_eq_map {X : Type} [Group X] (S : CubeSetting X)
    (A : Subgroup SL(6, ZMod 2)) : S.img A = A.map (markHom S) := rfl

private theorem markHom_injective {X : Type} [Group X] (S : CubeSetting X) :
    Function.Injective (markHom S) := by
  intro a b h
  apply S.eL.symm.injective
  apply Subtype.coe_injective
  exact h

private theorem rho_mark {X : Type} [Group X] (S : CubeSetting X) (g : SL(6, ZMod 2)) :
    S.ρ (markHom S g) = cubeAct g := by
  have h := S.hρ (S.eL.symm g)
  rwa [MulEquiv.apply_symm_apply] at h

private theorem rho_z_eq {X : Type} [Group X] (S : CubeSetting X) :
    S.ρ S.z = cubeAct CFSG.Holt.SL6.stdTransvection := by
  rw [show S.z = markHom S CFSG.Holt.SL6.stdTransvection from rfl]
  exact rho_mark S _

private theorem orderOf_b {X : Type} [Group X] (S : CubeSetting X) : orderOf S.b = 3 := by
  rw [CubeSetting.b, Subgroup.orderOf_coe, MulEquiv.orderOf_eq (S.eL.symm) bStd, orderOf_bStd]

private theorem mem_centralizer_z_iff {X : Type} [Group X] (S : CubeSetting X) {c : X} :
    c ∈ Subgroup.centralizer ({S.z} : Set X) ↔ S.z * c = c * S.z := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h; exact h S.z (by simp)
  · intro h x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h

private def KerSub {X : Type} [Group X] (S : CubeSetting X) : Subgroup X where
  carrier := {c | c ∈ Subgroup.centralizer ({S.z} : Set X) ∧
    ∀ w ∈ Wsp, S.ρ c w = w}
  one_mem' := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro w _
    rw [map_one]
    rfl
  mul_mem' := by
    rintro c d ⟨hcC, hcW⟩ ⟨hdC, hdW⟩
    refine ⟨Subgroup.mul_mem _ hcC hdC, ?_⟩
    intro w hw
    rw [map_mul]
    change S.ρ c (S.ρ d w) = w
    rw [hdW w hw, hcW w hw]
  inv_mem' := by
    rintro c ⟨hcC, hcW⟩
    refine ⟨Subgroup.inv_mem _ hcC, ?_⟩
    intro w hw
    have h2 : S.ρ c⁻¹ (S.ρ c w) = w := by
      change (S.ρ c⁻¹ * S.ρ c) w = w
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    rwa [hcW w hw] at h2

private theorem rho_mem_Wsp_of_mem_centralizer {X : Type} [Group X] (S : CubeSetting X) {c : X}
    (hc : c ∈ Subgroup.centralizer ({S.z} : Set X))
    {w : CFSG.RankThree.GF2n.Smith81.A5Cube.Cube (ZMod 2)}
    (hw : w ∈ Wsp) : S.ρ c w ∈ Wsp := by
  change w ∈ LinearMap.range (cubeAct CFSG.Holt.SL6.stdTransvection - 1) at hw
  change S.ρ c w ∈ LinearMap.range (cubeAct CFSG.Holt.SL6.stdTransvection - 1)
  obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hw
  refine LinearMap.mem_range.mpr ⟨S.ρ c v, ?_⟩
  have hzc : S.z * c = c * S.z := (Subgroup.mem_centralizer_iff.mp hc) S.z (by simp)
  have hcomm : S.ρ S.z * S.ρ c = S.ρ c * S.ρ S.z := by
    rw [← map_mul, ← map_mul, hzc]
  have happ : S.ρ S.z (S.ρ c v) = S.ρ c (S.ρ S.z v) := by
    have h2 := congrArg (fun f => f v) hcomm
    simpa only [Module.End.mul_apply] using h2
  rw [← hv, ← rho_z_eq S]
  change (S.ρ S.z - 1) (S.ρ c v) = S.ρ c ((S.ρ S.z - 1) v)
  simp only [LinearMap.sub_apply, map_sub, Module.End.one_apply, happ]

private theorem conj_mem_KerSub_of_mem_centralizer {X : Type} [Group X] (S : CubeSetting X)
    {c : X} (hc : c ∈ Subgroup.centralizer ({S.z} : Set X)) {k : X} (hk : k ∈ KerSub S) :
    c * k * c⁻¹ ∈ KerSub S := by
  obtain ⟨hkC, hkW⟩ := hk
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hkC) (Subgroup.inv_mem _ hc), ?_⟩
  intro w hw
  have h1 : S.ρ c⁻¹ w ∈ Wsp :=
    rho_mem_Wsp_of_mem_centralizer S (Subgroup.inv_mem _ hc) hw
  calc S.ρ (c * k * c⁻¹) w = S.ρ c (S.ρ k (S.ρ c⁻¹ w)) := by
        simp only [map_mul, Module.End.mul_apply]
    _ = S.ρ c (S.ρ c⁻¹ w) := by rw [hkW _ h1]
    _ = w := by
        change (S.ρ c * S.ρ c⁻¹) w = w
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl

private theorem Sgrp_le_KerSub {X : Type} [Group X] (S : CubeSetting X) :
    S.img Sgrp ≤ KerSub S := by
  intro c hc
  rw [img_eq_map, Subgroup.mem_map] at hc
  obtain ⟨g, hg, rfl⟩ := hc
  refine ⟨?_, ?_⟩
  · rw [mem_centralizer_z_iff S]
    rw [show S.z = markHom S CFSG.Holt.SL6.stdTransvection from rfl]
    rw [← map_mul, ← map_mul, comm_stdTransvection_of_mem_Sgrp g hg]
  · intro w hw
    rw [rho_mark S]
    exact cubeAct_apply_eq_of_mem_Sgrp hg hw

private theorem isPGroup_img_Sgrp {X : Type} [Group X] (S : CubeSetting X) :
    IsPGroup 2 (S.img Sgrp) := by
  rw [img_eq_map]
  exact isPGroup_Sgrp.map (markHom S)

private theorem z_mem_img_Sgrp {X : Type} [Group X] (S : CubeSetting X) :
    S.z ∈ S.img Sgrp := by
  rw [img_eq_map, Subgroup.mem_map]
  exact ⟨CFSG.Holt.SL6.stdTransvection, Subgroup.mem_sup_left stdTransvection_mem_Sone, rfl⟩

private theorem commutator_mem_zpowers_img_Sgrp {X : Type} [Group X] (S : CubeSetting X)
    (x : X) (hx : x ∈ S.img Sgrp) (y : X) (hy : y ∈ S.img Sgrp) :
    x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers S.z := by
  rw [img_eq_map, Subgroup.mem_map] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have hcomm := commutator_mem_zpowers_of_mem_Sgrp a b ha hb
  have hmem : markHom S (a * b * a⁻¹ * b⁻¹) ∈
      (Subgroup.zpowers CFSG.Holt.SL6.stdTransvection).map (markHom S) :=
    (Subgroup.mem_map).mpr ⟨_, hcomm, rfl⟩
  rw [MonoidHom.map_zpowers] at hmem
  have hz : S.z = markHom S CFSG.Holt.SL6.stdTransvection := rfl
  rw [hz]
  simpa only [map_mul, map_inv] using hmem

private theorem imgDgrp_le_centralizer {X : Type} [Group X] (S : CubeSetting X) :
    S.img Dgrp ≤ Subgroup.centralizer ({S.z} : Set X) := by
  intro d hd
  rw [img_eq_map, Subgroup.mem_map] at hd
  obtain ⟨a, ha, rfl⟩ := hd
  rw [mem_centralizer_z_iff S]
  rw [show S.z = markHom S CFSG.Holt.SL6.stdTransvection from rfl]
  rw [← map_mul, ← map_mul, comm_stdTransvection_of_mem_Jgrp a (Dgrp_le_Jgrp ha)]

private theorem imgDgrp_le_normalizer_KerSub {X : Type} [Group X] (S : CubeSetting X) :
    S.img Dgrp ≤ Subgroup.normalizer (KerSub S : Set X) := by
  intro d hd
  have hdC : d ∈ Subgroup.centralizer ({S.z} : Set X) := imgDgrp_le_centralizer S hd
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    exact conj_mem_KerSub_of_mem_centralizer S hdC hk
  · intro hk
    have hk' := conj_mem_KerSub_of_mem_centralizer S (Subgroup.inv_mem _ hdC) hk
    rwa [show d⁻¹ * (d * k * d⁻¹) * (d⁻¹)⁻¹ = k from by group] at hk'

private theorem nonempty_mulEquiv_imgDgrp {X : Type} [Group X] (S : CubeSetting X) :
    Nonempty (↥(S.img Dgrp) ≃* SL(3, ZMod 2)) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Dgrp
  exact ⟨(Subgroup.equivMapOfInjective Dgrp (markHom S) (markHom_injective S)).symm.trans e⟩

private theorem b_mem_imgDgrp {X : Type} [Group X] (S : CubeSetting X) :
    S.b ∈ S.img Dgrp := by
  rw [img_eq_map, Subgroup.mem_map]
  exact ⟨bStd, bStd_mem_Dgrp, rfl⟩

private theorem imgDgrp_le_normalizer_imgSgrp {X : Type} [Group X] (S : CubeSetting X) :
    S.img Dgrp ≤ Subgroup.normalizer (S.img Sgrp : Set X) := by
  intro d hd
  rw [img_eq_map, Subgroup.mem_map] at hd
  obtain ⟨a, ha, rfl⟩ := hd
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [img_eq_map, Subgroup.mem_map] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    rw [img_eq_map, Subgroup.mem_map]
    refine ⟨a * g * a⁻¹, conj_mem_Sgrp_of_mem_Jgrp a g (Dgrp_le_Jgrp ha) hg, ?_⟩
    simp only [map_mul, map_inv]
  · intro hx
    rw [img_eq_map, Subgroup.mem_map] at hx
    obtain ⟨g, hg, hgx⟩ := hx
    rw [img_eq_map, Subgroup.mem_map]
    refine ⟨a⁻¹ * g * a, ?_, ?_⟩
    · simpa only [inv_inv] using
        conj_mem_Sgrp_of_mem_Jgrp a⁻¹ g (Subgroup.inv_mem Jgrp (Dgrp_le_Jgrp ha)) hg
    · have hx_eq : x = markHom S a⁻¹ * markHom S g * markHom S a := by
        rw [hgx]
        simp only [map_inv]
        group
      rw [hx_eq]
      simp only [map_mul, map_inv]

private theorem centralizer_b_KerSub_le {X : Type} [Group X] (S : CubeSetting X)
    (hB : ∀ c : X, c * S.z = S.z * c → c * S.b = S.b * c → c ∈ S.img (Sgrp ⊔ Jgrp)) :
    ∀ x ∈ KerSub S, x * S.b = S.b * x → x ∈ S.img Sgrp := by
  intro x hxK hxb
  obtain ⟨hxC, hxW⟩ := hxK
  have hzx : x * S.z = S.z * x := ((mem_centralizer_z_iff S).mp hxC).symm
  have hxSJ : x ∈ S.img (Sgrp ⊔ Jgrp) := hB x hzx hxb
  rw [img_eq_map, Subgroup.mem_map] at hxSJ
  obtain ⟨g, hg, rfl⟩ := hxSJ
  rw [img_eq_map, Subgroup.mem_map]
  refine ⟨g, ?_, rfl⟩
  refine mem_Sgrp_of_cubeAct_eq_on_Wsp (g := g) hg ?_
  intro w hw
  have h := hxW w hw
  rwa [rho_mark S] at h

private theorem KerSub_le_imgSgrp {X : Type} [Group X] [Finite X] (S : CubeSetting X)
    (hB : ∀ c : X, c * S.z = S.z * c → c * S.b = S.b * c → c ∈ S.img (Sgrp ⊔ Jgrp)) :
    KerSub S ≤ S.img Sgrp := by
  refine CFSG.StandardType.FrameRoute.FS81.le_of_selfNormalizing_l3Two
    (S := KerSub S) (P := S.img Sgrp) (D := S.img Dgrp)
    (σ := S.z) (b := S.b)
    (hPS := Sgrp_le_KerSub S) (hP := isPGroup_img_Sgrp S) (hσP := z_mem_img_Sgrp S)
    (hSσ := ?_) (hPP := commutator_mem_zpowers_img_Sgrp S)
    (hDS := imgDgrp_le_normalizer_KerSub S)
    (hDP := imgDgrp_le_normalizer_imgSgrp S)
    (hD := nonempty_mulEquiv_imgDgrp S) (hbD := b_mem_imgDgrp S) (hb := orderOf_b S)
    (hC := centralizer_b_KerSub_le S hB)
  intro s hs
  exact ((mem_centralizer_z_iff S).mp hs.1).symm

theorem mem_img_Sgrp_of_trivial_on_Wsp {X : Type} [Group X] [Finite X] (S : CubeSetting X)
    (hB : ∀ c : X, c * S.z = S.z * c → c * S.b = S.b * c → c ∈ S.img (Sgrp ⊔ Jgrp))
    {c : X} (hz : c * S.z = S.z * c) (hW : ∀ w ∈ Wsp, S.ρ c w = w) : c ∈ S.img Sgrp :=
  KerSub_le_imgSgrp S hB ⟨(mem_centralizer_z_iff S).mpr hz.symm, hW⟩

theorem conj_mem_img_Sgrp {X : Type} [Group X] [Finite X] (S : CubeSetting X)
    (hB : ∀ c : X, c * S.z = S.z * c → c * S.b = S.b * c → c ∈ S.img (Sgrp ⊔ Jgrp))
    {c : X} (hz : c * S.z = S.z * c) {x : X} (hx : x ∈ S.img Sgrp) :
    c * x * c⁻¹ ∈ S.img Sgrp := by
  refine KerSub_le_imgSgrp S hB ?_
  have hcC : c ∈ Subgroup.centralizer ({S.z} : Set X) := (mem_centralizer_z_iff S).mpr hz.symm
  have hxK : x ∈ KerSub S := Sgrp_le_KerSub S hx
  obtain ⟨hxC, hxW⟩ := hxK
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hcC hxC) (Subgroup.inv_mem _ hcC), ?_⟩
  intro w hw
  have h1 : S.ρ c⁻¹ w ∈ Wsp :=
    rho_mem_Wsp_of_mem_centralizer S (Subgroup.inv_mem _ hcC) hw
  calc S.ρ (c * x * c⁻¹) w = S.ρ c (S.ρ x (S.ρ c⁻¹ w)) := by
        simp only [map_mul, Module.End.mul_apply]
    _ = S.ρ c (S.ρ c⁻¹ w) := by rw [hxW _ h1]
    _ = w := by
        change (S.ρ c * S.ρ c⁻¹) w = w
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl

end CFSG.StandardType.FF81.CentE6
