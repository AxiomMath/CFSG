module

public import CFSG.Quasithin.Background.F918Z8g
public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.Quasithin.EmptyFaithful.S153ZE

public section

namespace CFSG.Quasithin

section

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem sxc_rk_autSec_add {A : Subgroup (MulAut Y)} {I J : Subgroup Y} (hAI : A ≤ stabSub I)
    (hAJ : A ≤ stabSub J) : rk (autSec A I J) + rk ↥(A ⊓ centSec I J) = rk A := by
  have := card_autSec_mul hAI hAJ
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', this]

omit [Finite Y] in
theorem sxc_mk_mem_fixV_autSec {B : Subgroup (MulAut Y)} {W J : Subgroup Y} (hBW : B ≤ stabSub W)
    (hBJ : B ≤ stabSub J) (w : ↥W) :
    (QuotientGroup.mk w : Sec W J) ∈ fixV (autSec B W J) ↔
      ∀ b ∈ B, b (w : Y) * (w : Y)⁻¹ ∈ J := by
  rw [autSec, mk_mem_fixV_autQuot]
  constructor
  · intro h b hb
    have hg : resHom W ⟨b, hBW hb⟩ ∈ autSub B W := mem_autSub.2 ⟨⟨b, hBW hb⟩, hb, rfl⟩
    have := h _ hg (autSub_le_stabSub_subgroupOf hBJ hg)
    rw [Subgroup.mem_subgroupOf] at this
    simpa [resHom_apply] using this
  · intro h g hg _
    obtain ⟨b, hb, rfl⟩ := mem_autSub.1 hg
    rw [Subgroup.mem_subgroupOf]
    simpa [resHom_apply] using h b hb

theorem sxc_nB_top {Q : Type} [CommGroup Q] [Finite Q] (B : Subgroup (MulAut Q)) :
    Z391.nB B (⊤ : Subgroup Q) = rkIdx (fixV B) := by
  have e1 : XMod.fixed ↥B (⊤ : Subgroup Q) = fixV B :=
    (fixed_eq_inf_fixV B ⊤).trans (top_inf_eq _)
  have e2 := rk_add_rkIdx (fixV B)
  have e3 : rk ↥(⊤ : Subgroup Q) = rk Q := rk_top
  unfold Z391.nB
  rw [e1, top_inf_eq, e3]
  omega

@[expose] def sxc_secInc {I J I₀ : Subgroup Y} (hI₀I : I₀ ≤ I) : Sec I₀ J →* Sec I J :=
  QuotientGroup.lift (J.subgroupOf I₀)
    ((QuotientGroup.mk' (J.subgroupOf I)).comp (Subgroup.inclusion hI₀I)) fun x hx =>
      (QuotientGroup.eq_one_iff _).2 (by simpa [Subgroup.mem_subgroupOf] using hx)

omit [Finite Y] in
theorem sxc_secInc_mk {I J I₀ : Subgroup Y} (hI₀I : I₀ ≤ I) (u : ↥I₀) :
    sxc_secInc (J := J) hI₀I (QuotientGroup.mk u) = QuotientGroup.mk ⟨(u : Y), hI₀I u.2⟩ := rfl

omit [Finite Y] in
theorem sxc_secInc_injective {I J I₀ : Subgroup Y} (hI₀I : I₀ ≤ I) :
    Function.Injective (sxc_secInc (J := J) hI₀I) := by
  intro a b hab
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      rw [sxc_secInc_mk, sxc_secInc_mk, QuotientGroup.eq] at hab
      rw [QuotientGroup.eq]
      simpa [Subgroup.mem_subgroupOf] using hab

omit [Finite Y] in
theorem sxc_range_secInc (I J : Subgroup Y) (S : Subgroup (Sec I J)) :
    (sxc_secInc (J := J) (d321f_secPre_le S)).range = S := by
  ext s
  constructor
  · rintro ⟨x, rfl⟩
    induction x using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨hu, h⟩ := d321f_mem_secPre.1 x.2
      exact h
  · intro hs
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨QuotientGroup.mk ⟨(x : Y), d321f_mem_secPre.2 ⟨x.2, hs⟩⟩, rfl⟩

omit [Finite Y] in
theorem sxc_rk_secPre (I J : Subgroup Y) (S : Subgroup (Sec I J)) :
    rk ↥S = rk (Sec (d321f_secPre I J S) J) := by
  have hinj := sxc_secInc_injective (J := J) (d321f_secPre_le S)
  have h1 : Nat.card ↥(sxc_secInc (J := J) (d321f_secPre_le S)).range =
      Nat.card (Sec (d321f_secPre I J S) J) :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  rw [sxc_range_secInc I J S] at h1
  unfold rk
  rw [h1]

theorem sxc_nB_secPre {B : Subgroup (MulAut Y)} {I J : Subgroup Y}
    (hBI : B ≤ stabSub I) (hBJ : B ≤ stabSub J) (S : Subgroup (Sec I J))
    (hBI₀ : B ≤ stabSub (d321f_secPre I J S)) :
    Z391.nB (autSec B I J) S = rkIdx (fixV (autSec B (d321f_secPre I J S) J)) := by
  set I₀ := d321f_secPre I J S with hI₀
  have hI₀I : I₀ ≤ I := d321f_secPre_le S
  have hinj := sxc_secInc_injective (J := J) hI₀I
  have hmap : S ⊓ fixV (autSec B I J) = (fixV (autSec B I₀ J)).map (sxc_secInc hI₀I) := by
    ext y
    constructor
    · rintro ⟨hyS, hyF⟩
      obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk_surjective y
      have hu₀ : u ∈ I₀ := d321f_mem_secPre.2 ⟨hu, hyS⟩
      exact ⟨QuotientGroup.mk ⟨u, hu₀⟩,
        (sxc_mk_mem_fixV_autSec hBI₀ hBJ ⟨u, hu₀⟩).2
          ((sxc_mk_mem_fixV_autSec hBI hBJ ⟨u, hu⟩).1 hyF), rfl⟩
    · rintro ⟨x, hx, rfl⟩
      induction x using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨hu, h⟩ := d321f_mem_secPre.1 x.2
        exact ⟨h, (sxc_mk_mem_fixV_autSec hBI hBJ ⟨(x : Y), hu⟩).2
          ((sxc_mk_mem_fixV_autSec hBI₀ hBJ x).1 hx)⟩
  have hrk : rk ↥(S ⊓ fixV (autSec B I J)) = rk ↥(fixV (autSec B I₀ J)) := by
    rw [hmap]
    unfold rk
    rw [Subgroup.card_map_of_injective hinj]
  have e1 : XMod.fixed ↥(autSec B I J) (⊤ : Subgroup (Sec I J)) = fixV (autSec B I J) :=
    (fixed_eq_inf_fixV _ ⊤).trans (top_inf_eq _)
  have e2 := rk_add_rkIdx (fixV (autSec B I₀ J))
  have e3 : rk ↥S = rk (Sec I₀ J) := sxc_rk_secPre I J S
  unfold Z391.nB
  rw [e1, hrk, e3]
  omega

end

end CFSG.Quasithin
