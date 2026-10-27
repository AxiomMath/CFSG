module

public import CFSG.Assembly.Defs
public import CFSG.Quasithin.EmptyFaithful.S153ZE

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

theorem rk_add_rk_ker {W Q : Type*} [CommGroup W] [Finite W] [CommGroup Q] (π : W →* Q)
    (hπ : Function.Surjective π) : rk Q + rk π.ker = rk W := by
  have : Finite Q := Finite.of_surjective π hπ
  have h := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup W) π
  rw [Subgroup.map_top_of_surjective π hπ, top_inf_eq, Subgroup.card_top, Subgroup.card_top] at h
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h]

variable {W : Type} [CommGroup W] [Finite W] {M : Subgroup (MulAut W)} {Q : Type} [CommGroup Q]
  [MulDistribMulAction ↥M Q]

theorem nB_top_le_rkIdx_fixV (π : W →* Q) (hπ : Function.Surjective π)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (A₀ : Subgroup ↥M) :
    nB A₀ (⊤ : Subgroup Q) ≤ rkIdx (fixV (A₀.map M.subtype)) := by
  classical
  have : Finite Q := Finite.of_surjective π hπ
  set A : Subgroup (MulAut W) := A₀.map M.subtype with hA
  unfold nB
  set F := XMod.fixed ↥A₀ (⊤ : Subgroup Q) with hF
  have himg : (fixV A).map π ≤ F := by
    rintro _ ⟨x, hx, rfl⟩
    refine XMod.mem_fixed.2 ⟨trivial, fun a => ?_⟩
    change (a : ↥M) • π x = π x
    rw [hπM]
    congr 1
    exact hx _ ⟨(a : ↥M), a.2, rfl⟩
  have h1 := B1More.card_map_mul_card_inf_ker (fixV A) π
  have h1' : rk ↥((fixV A).map π) + rk ↥(fixV A ⊓ π.ker) = rk ↥(fixV A) := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h1]
  have h2 : rk ↥((fixV A).map π) ≤ rk ↥F := rk_mono himg
  have h3 : rk ↥(fixV A ⊓ π.ker) ≤ rk π.ker := rk_mono inf_le_right
  have h4 := rk_add_rk_ker π hπ
  have h5 := rk_add_rkIdx (fixV A)
  have h6 : rk ↥((⊤ : Subgroup Q) ⊓ F) = rk ↥F := by rw [top_inf_eq]
  have h7 : rk ↥(⊤ : Subgroup Q) = rk Q := rk_top
  have h8 : rk ↥F ≤ rk Q := by
    have := rk_mono (le_top : F ≤ ⊤)
    rwa [rk_top] at this
  rw [h6, h7]
  omega

theorem rkIdx_fixV_autSec_le_nB [Finite Q] (π : W →* Q)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (A₀ : Subgroup ↥M) (V : Subgroup W) :
    rkIdx (fixV (autSec (A₀.map M.subtype) V (V ⊓ π.ker))) ≤ nB A₀ (V.map π) := by
  classical
  set A : Subgroup (MulAut W) := A₀.map M.subtype with hA
  set U : Subgroup W := V ⊓ π.ker with hU
  unfold nB
  set F := XMod.fixed ↥A₀ (⊤ : Subgroup Q) with hF
  have hUV : U ≤ V := inf_le_left
  have hcard : Nat.card (Sec V U) = Nat.card ↥(V.map π) := by
    have h1 := card_sec_mul hUV
    have h2 := B1More.card_map_mul_card_inf_ker V π
    have hpos : 0 < Nat.card ↥U := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  have hrkSec : rk (Sec V U) = rk ↥(V.map π) := by
    unfold rk
    rw [hcard]
  let θ : Sec V U →* Q :=
    QuotientGroup.lift (U.subgroupOf V) (π.comp V.subtype) (fun x hx => hx.2)
  have hθ : ∀ v : ↥V, θ (QuotientGroup.mk v) = π (v : W) := fun v => rfl
  have hθinj : Function.Injective θ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [hθ, hθ] at hab
        rw [QuotientGroup.eq]
        refine ⟨(a⁻¹ * b).2, ?_⟩
        show π (((a⁻¹ * b : ↥V)) : W) = 1
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hab, inv_mul_cancel]
  have hle : V.map π ⊓ F ≤ (fixV (autSec A V U)).map θ := by
    rintro y ⟨hyV, hyF⟩
    obtain ⟨v, hv, rfl⟩ := hyV
    refine ⟨QuotientGroup.mk ⟨v, hv⟩, ?_, rfl⟩
    show (QuotientGroup.mk ⟨v, hv⟩ : Sec V U) ∈ fixV (autQuot (autSub A V) (U.subgroupOf V))
    rw [mk_mem_fixV_autQuot]
    intro g hg _
    obtain ⟨g', hg'A, rfl⟩ := mem_autSub.mp hg
    obtain ⟨a, ha, hga⟩ := Subgroup.mem_map.mp hg'A
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, ?_⟩
    · exact V.mul_mem ((g'.2 v).2 hv) (V.inv_mem hv)
    · show π (g'.1 v * v⁻¹) = 1
      have h1 : a • π v = π v := (XMod.mem_fixed.1 hyF).2 ⟨a, ha⟩
      change (a : ↥M) • π v = π v at h1
      rw [hπM] at h1
      have h2 : (g'.1 : MulAut W) = (a : MulAut W) := hga.symm
      rw [map_mul, map_inv, h2, h1, mul_inv_cancel]
  have h3 : rk ↥(V.map π ⊓ F) ≤ rk ↥(fixV (autSec A V U)) := by
    calc rk ↥(V.map π ⊓ F) ≤ rk ↥((fixV (autSec A V U)).map θ) := rk_mono hle
      _ = rk ↥(fixV (autSec A V U)) := by
        unfold rk
        rw [Subgroup.card_map_of_injective hθinj]
  have h4 := rk_add_rkIdx (fixV (autSec A V U))
  omega

end CFSG.Quasithin.Z391
