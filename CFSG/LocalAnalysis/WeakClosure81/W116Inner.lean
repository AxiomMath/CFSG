module

public import CFSG.LocalAnalysis.WeakClosure81.W115Gen
public import CFSG.Quasithin.H13.A5M22HatAut
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22ReducibleMBound
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43RedA

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem w116_inner_ge
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hq : IsQuasisimple ↥L) (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (hSp : IsSpor (↥L ⧸ Subgroup.center ↥L) .M22) (hirr : IsIrrOn L ⊤ ⊥)
    {s : MulAut W} (hsL : s ∈ L) (hs2 : orderOf s = 2) :
    4 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨z0, hz0ord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(Subgroup.center ↥L)) 3 (by rw [hZ])
  let zL : ↥L := (z0 : ↥L)
  let z : MulAut W := (zL : MulAut W)
  have hzL_ord : orderOf zL = 3 := (Subgroup.orderOf_coe z0).trans hz0ord
  have hz_ord : orderOf z = 3 := (Subgroup.orderOf_coe zL).trans hzL_ord
  have hz3 : z ^ 3 = 1 := by
    rw [← hz_ord]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz_ord
    omega
  have hzL : z ∈ L := zL.2
  have hzc : ∀ h ∈ L, h * z = z * h := by
    intro h hh
    have hc := Subgroup.mem_center_iff.mp z0.2 (⟨h, hh⟩ : ↥L)
    have hc' := congrArg (fun x : ↥L => (x : MulAut W)) hc
    simpa [z, zL] using hc'
  have hfpf : ∀ w : W, z w = w → w = 1 :=
    fun w hw => s16ku43_center_fixes_only_one hirr hzL hzc hz1 hw
  let sL : ↥L := ⟨s, hsL⟩
  have hs2mul : s * s = 1 := by
    rw [← pow_two, ← hs2, pow_orderOf_eq_one]
  have hsL2 : sL * sL = 1 := by
    apply Subtype.ext
    simpa [sL] using hs2mul
  have hs_not_center : sL ∉ Subgroup.center ↥L := by
    intro hmem
    have hdvd := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hmem
    have hord : orderOf sL = 2 := by
      rw [← Subgroup.orderOf_coe sL]
      exact hs2
    rw [hZ, hord] at hdvd
    norm_num at hdvd
  let Lbar : Type := ↥L ⧸ Subgroup.center ↥L
  let π : ↥L →* Lbar := QuotientGroup.mk' (Subgroup.center ↥L)
  let sbar : Lbar := π sL
  have hsbar2 : sbar * sbar = 1 := by
    change π sL * π sL = 1
    rw [← map_mul, hsL2, map_one]
  have hsbar_ne : sbar ≠ 1 := by
    intro h
    have hmem : sL ∈ Subgroup.center ↥L := by
      change π sL = 1 at h
      exact (QuotientGroup.eq_one_iff sL).mp h
    exact hs_not_center hmem
  have hZLbar : Subgroup.center Lbar = ⊥ := by
    haveI : Group.IsPerfect ↥L := hq.1
    exact Group.IsPerfect.center_quotient_center_eq_bot (G := ↥L)
  obtain ⟨e₀⟩ := hSp
  let e : Lbar ≃* ↥H.Mathieu.mog22 := e₀.trans H.Mathieu.mog22EquivM22.symm
  set g : ↥H.Mathieu.mog22 := e sbar with hgdef
  set β : MulAut ↥H.Mathieu.mog22 := MulAut.conj g with hβdef
  have hg2 : g * g = 1 := by
    rw [hgdef, ← map_mul, hsbar2, map_one]
  have hβ2 : β * β = 1 := by
    rw [hβdef, ← map_mul, hg2, map_one]
  have hβ1 : β ≠ 1 := by
    intro hβ
    have hg_cen : g ∈ Subgroup.center ↥H.Mathieu.mog22 := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := congrArg (fun f : MulAut ↥H.Mathieu.mog22 => f x) hβ
      rw [hβdef, MulAut.conj_apply, MulAut.one_apply] at h1
      have h2 : g * x = x * g := by
        have h3 := congrArg (fun y => y * g) h1
        simpa [mul_assoc] using h3
      exact h2.symm
    have hsbar_cen : sbar ∈ Subgroup.center Lbar := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply e.injective
      rw [map_mul, map_mul, ← hgdef]
      exact Subgroup.mem_center_iff.mp hg_cen (e x)
    rw [hZLbar, Subgroup.mem_bot] at hsbar_cen
    exact hsbar_ne hsbar_cen
  obtain ⟨n₁, n₂, n₃, hn11⟩ := H13.A5.M22Hat.exists_orderOf_eleven β hβ2 hβ1
  let a₁ : Lbar := e.symm n₁
  let a₂ : Lbar := e.symm n₂
  let a₃ : Lbar := e.symm n₃
  obtain ⟨γ₁, hγ₁⟩ := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)) a₁
  obtain ⟨γ₂, hγ₂⟩ := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)) a₂
  obtain ⟨γ₃, hγ₃⟩ := (QuotientGroup.mk'_surjective (Subgroup.center ↥L)) a₃
  have hc₁L : (γ₁ : MulAut W) * s * (γ₁ : MulAut W)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem γ₁.2 hsL) (L.inv_mem γ₁.2)
  have hc₂L : (γ₂ : MulAut W) * s * (γ₂ : MulAut W)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem γ₂.2 hsL) (L.inv_mem γ₂.2)
  have hc₃L : (γ₃ : MulAut W) * s * (γ₃ : MulAut W)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem γ₃.2 hsL) (L.inv_mem γ₃.2)
  let c₁L : ↥L := ⟨(γ₁ : MulAut W) * s * (γ₁ : MulAut W)⁻¹, hc₁L⟩
  let c₂L : ↥L := ⟨(γ₂ : MulAut W) * s * (γ₂ : MulAut W)⁻¹, hc₂L⟩
  let c₃L : ↥L := ⟨(γ₃ : MulAut W) * s * (γ₃ : MulAut W)⁻¹, hc₃L⟩
  let y : MulAut W := s * ((γ₁ : MulAut W) * s * (γ₁ : MulAut W)⁻¹) *
    ((γ₂ : MulAut W) * s * (γ₂ : MulAut W)⁻¹) *
    ((γ₃ : MulAut W) * s * (γ₃ : MulAut W)⁻¹)
  have hyL : y ∈ L := by
    dsimp only [y]
    exact L.mul_mem (L.mul_mem (L.mul_mem hsL hc₁L) hc₂L) hc₃L
  let yM : ↥L := ⟨y, hyL⟩
  have hyM_product : yM = sL * c₁L * c₂L * c₃L := by
    apply Subtype.ext
    simp [yM, y, sL, c₁L, c₂L, c₃L]
  have hπc₁ : π c₁L = a₁ * sbar * a₁⁻¹ := by
    have hc : c₁L = γ₁ * sL * γ₁⁻¹ := by
      apply Subtype.ext
      simp [c₁L, sL]
    rw [hc]
    simp only [map_mul, map_inv]
    rw [hγ₁]
  have hπc₂ : π c₂L = a₂ * sbar * a₂⁻¹ := by
    have hc : c₂L = γ₂ * sL * γ₂⁻¹ := by
      apply Subtype.ext
      simp [c₂L, sL]
    rw [hc]
    simp only [map_mul, map_inv]
    rw [hγ₂]
  have hπc₃ : π c₃L = a₃ * sbar * a₃⁻¹ := by
    have hc : c₃L = γ₃ * sL * γ₃⁻¹ := by
      apply Subtype.ext
      simp [c₃L, sL]
    rw [hc]
    simp only [map_mul, map_inv]
    rw [hγ₃]
  have hπy0 : π yM = sbar * (a₁ * sbar * a₁⁻¹) * (a₂ * sbar * a₂⁻¹) *
      (a₃ * sbar * a₃⁻¹) := by
    rw [hyM_product]
    simp only [map_mul]
    rw [hπc₁, hπc₂, hπc₃]
  have hE : e (π yM) = g * (n₁ * g * n₁⁻¹) * (n₂ * g * n₂⁻¹) *
      (n₃ * g * n₃⁻¹) := by
    rw [hπy0]
    simp only [map_mul, map_inv]
    rw [← hgdef]
    simp only [a₁, a₂, a₃, MulEquiv.apply_symm_apply]
  have hEt : e (π yM) = β n₁ * n₁⁻¹ * (n₂ * β (n₂⁻¹ * n₃) * n₃⁻¹) := by
    rw [hE, hβdef]
    simp only [MulAut.conj_apply]
    rw [inv_eq_of_mul_eq_one_right hg2]
    group
  have hπy : π yM = e.symm (β n₁ * n₁⁻¹ * (n₂ * β (n₂⁻¹ * n₃) * n₃⁻¹)) := by
    apply e.injective
    rw [hEt, MulEquiv.apply_symm_apply]
  have hπord : orderOf (π yM) = 11 := by
    rw [hπy, MulEquiv.orderOf_eq, hn11]
  have hy11M : 11 ∣ orderOf yM := by
    rw [← hπord]
    exact orderOf_map_dvd π yM
  have hy11 : 11 ∣ orderOf y := by
    rw [show y = (yM : MulAut W) from rfl, Subgroup.orderOf_coe yM]
    exact hy11M
  have h10 : 10 ≤ rkIdx (fixV (Subgroup.zpowers y)) :=
    ten_le_rkIdx_of_eleven hW hy11
  have h4 : rkIdx (fixV (Subgroup.zpowers y)) ≤
      4 * rkIdx (fixV (Subgroup.zpowers s)) := by
    have hp := w115_rkIdx_fixV_prod_four_le hW s
      ((γ₁ : MulAut W) * s * (γ₁ : MulAut W)⁻¹)
      ((γ₂ : MulAut W) * s * (γ₂ : MulAut W)⁻¹)
      ((γ₃ : MulAut W) * s * (γ₃ : MulAut W)⁻¹)
    rw [H13.A5.M22Hat.rkIdx_fixV_conj (γ₁ : MulAut W) s,
      H13.A5.M22Hat.rkIdx_fixV_conj (γ₂ : MulAut W) s,
      H13.A5.M22Hat.rkIdx_fixV_conj (γ₃ : MulAut W) s] at hp
    dsimp only [y] at hp ⊢
    omega
  have heven : Even (rkIdx (fixV (Subgroup.zpowers s))) :=
    w115_even_rkIdx_fixV_of_commute hW hz3 hfpf (hzc s hsL).symm
  obtain ⟨k, hk⟩ := heven
  omega

end CFSG.LocalAnalysis.WeakClosure81.W115
