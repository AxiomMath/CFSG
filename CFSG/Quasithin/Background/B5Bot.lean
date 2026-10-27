module

public import CFSG.Quasithin.Background.B5Sec

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace B5

section Bot

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem card_fixV_autSec_bot {A : Subgroup (MulAut V)} {W : Subgroup V} (hAW : A ≤ stabSub W) :
    Nat.card (fixV (autSec A W ⊥)) = Nat.card ↥(W ⊓ fixV A) := by
  set f : ↥W →* Sec W ⊥ := QuotientGroup.mk' ((⊥ : Subgroup V).subgroupOf W) with hf
  have hbot : (⊥ : Subgroup V).subgroupOf W = ⊥ := Subgroup.bot_subgroupOf W
  have hinj : Function.Injective f := by
    rw [hf, ← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hbot]
  have h1 : fixV (autSec A W ⊥) = (fixV (autSub A W)).map f := by
    ext x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨w, ?_, rfl⟩
      rw [mem_fixV_autSub]
      intro g hg hgs
      have hstab : resHom W ⟨g, hgs⟩ ∈ stabSub ((⊥ : Subgroup V).subgroupOf W) := by
        intro u
        rw [hbot, Subgroup.mem_bot, Subgroup.mem_bot]
        exact MulEquiv.map_eq_one_iff (resHom W ⟨g, hgs⟩)
      have := (mk_mem_fixV_autQuot (X := autSub A W) (U := (⊥ : Subgroup V).subgroupOf W)
        (v := w)).1 hx (resHom W ⟨g, hgs⟩) (mem_autSub.2 ⟨⟨g, hgs⟩, hg, rfl⟩) hstab
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_bot] at this
      exact mul_inv_eq_one.1 this
    · rintro ⟨w', hw', hw'x⟩
      rw [← hw'x]
      refine (mk_mem_fixV_autQuot (X := autSub A W) (U := (⊥ : Subgroup V).subgroupOf W)
        (v := w')).2 fun g hg _ => ?_
      rw [hw' g hg, mul_inv_cancel]
      exact Subgroup.one_mem _
  rw [h1, Subgroup.card_map_of_injective hinj]
  have := map_subtype_fixV_autSub (A := A) (U := W) hAW
  rw [← this, Subgroup.card_map_of_injective W.subtype_injective]


omit [Finite V] in
theorem exists_le_autSec_eq {X A : Subgroup (MulAut V)} {W U : Subgroup V} (hXW : X ≤ stabSub W)
    (hXU : X ≤ stabSub U) (hAX : A ≤ X) {B' : Subgroup (MulAut (Sec W U))}
    (hB' : B' ≤ autSec A W U) : ∃ B₀ : Subgroup (MulAut V), B₀ ≤ A ∧ autSec B₀ W U = B' := by
  set ψ := secHom X hXW hXU with hψ
  refine ⟨A ⊓ (B'.comap ψ).map X.subtype, inf_le_left, ?_⟩
  have hB₀X : A ⊓ (B'.comap ψ).map X.subtype ≤ X := inf_le_left.trans hAX
  rw [← map_secHom_eq_autSec X hXW hXU hB₀X]
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : (g : MulAut V) ∈ A ⊓ (B'.comap ψ).map X.subtype := hg
    obtain ⟨g', hg', hg'g⟩ := hg'.2
    have : g' = g := Subtype.ext hg'g
    rw [this] at hg'
    exact hg'
  · intro hy
    have hy' : y ∈ (A.subgroupOf X).map ψ := by
      rw [map_secHom_eq_autSec X hXW hXU hAX]; exact hB' hy
    obtain ⟨g, hg, rfl⟩ := hy'
    refine ⟨g, ?_, rfl⟩
    exact ⟨hg, ⟨g, hy, rfl⟩⟩


theorem isFFStarOffender_autSec_bot {X A : Subgroup (MulAut V)} (hA : IsFFStarOffender X A)
    {W : Subgroup V} (hXW : X ≤ stabSub W) (hfaith : A ⊓ centSec W ⊥ = ⊥) :
    IsFFStarOffender (autSec X W ⊥) (autSec A W ⊥) := by
  have hAX := hA.1
  have hXU : X ≤ stabSub (⊥ : Subgroup V) := fun g _ u => by
    simp only [Subgroup.mem_bot, MulEquiv.map_eq_one_iff]
  have hcard : ∀ B : Subgroup (MulAut V), B ≤ A → Nat.card (autSec B W ⊥) = Nat.card B := by
    intro B hBA
    have h1 := card_autSec_mul (A := B) (W := W) (U := ⊥) ((hBA.trans hAX).trans hXW)
      ((hBA.trans hAX).trans hXU)
    have h2 : B ⊓ centSec W ⊥ = ⊥ := by
      rw [eq_bot_iff, ← hfaith]
      exact inf_le_inf hBA le_rfl
    rw [h2, Subgroup.card_bot, mul_one] at h1
    exact h1
  refine ⟨autSec_mono hAX W ⊥, ?_, isElemAbelian2_autSec W ⊥ hA.2.2.1, ?_⟩
  · intro hbot
    apply hA.2.1
    have h1 := hcard A le_rfl
    rw [hbot, Subgroup.card_bot] at h1
    exact Subgroup.card_eq_one.1 h1.symm
  · intro B' hB'
    obtain ⟨B₀, hB₀A, rfl⟩ := exists_le_autSec_eq hXW hXU hAX hB'
    rw [hcard B₀ hB₀A, hcard A le_rfl,
      card_fixV_autSec_bot ((hB₀A.trans hAX).trans hXW),
      card_fixV_autSec_bot (hAX.trans hXW)]
    exact (B1.card_inf_fixV_aux hA hB₀A W).1

end Bot

end B5

end CFSG.Quasithin
