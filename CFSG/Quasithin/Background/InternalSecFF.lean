module

public import CFSG.Quasithin.Background.InternalSecData

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.QuasithinUnique.Bridge
open scoped IsMulCommutative

section Abstract

variable {V : Type} [CommGroup V] [Finite V] {X : Subgroup (MulAut V)} {C : Subgroup V}
  (hX : X ≤ stabSub C) (hf : X ⊓ centSec ⊤ C = ⊥)

include hX hf

omit [Finite V] in
theorem card_autSec_eq {A : Subgroup (MulAut V)} (hAX : A ≤ X) :
    Nat.card ↥(autSec A ⊤ C) = Nat.card ↥A := by
  have h := card_autSec_mul (A := A) (W := ⊤) (U := C) (le_stabSub_top A) (hAX.trans hX)
  have hb : A ⊓ centSec ⊤ C = ⊥ := le_bot_iff.1 (hf ▸ inf_le_inf_right _ hAX)
  rw [hb, Subgroup.card_bot, mul_one] at h
  exact h

omit hX hf in
theorem card_fixV_le_autSec (A : Subgroup (MulAut V)) :
    Nat.card ↥(fixV A) ≤ Nat.card ↥(fixV (autSec A ⊤ C)) * Nat.card ↥C := by
  have h := card_inf_fixV_le_autSec (A := A) (W := ⊤) (U := C) le_top (le_stabSub_top A)
  rw [top_inf_eq] at h
  exact h.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le inf_le_left))

omit [Finite V] hf in
theorem stab_of_le {A : Subgroup (MulAut V)} (hAX : A ≤ X) : A ≤ stabSub ⊤ ⊓ stabSub C :=
  fun a ha => ⟨mem_stabSub_top a, hX (hAX ha)⟩

omit [Finite V] hX in
theorem not_le_centSec {A : Subgroup (MulAut V)} (hAX : A ≤ X) (hA1 : A ≠ ⊥) :
    ¬ A ≤ centSec ⊤ C :=
  fun h => hA1 (le_bot_iff.1 (hf ▸ le_inf hAX h))

theorem isFFModule_autSec_of_faithful (hFF : IsFFModule X) : IsFFModule (autSec X ⊤ C) := by
  obtain ⟨A, hAX, hA1, hAab, hcard⟩ := hFF
  refine ⟨autSec A ⊤ C, autSec_mono hAX ⊤ C,
    CFSG.QuasithinUnique.Bridge.autSec_ne_bot (stab_of_le hX hAX) (not_le_centSec hf hAX hA1),
    CFSG.QuasithinUnique.Bridge.isElemAbelian2_autSec hAab (stab_of_le hX hAX), ?_⟩
  have h1 := card_autSec_eq hX hf hAX
  have h2 := card_fixV_le_autSec (C := C) A
  have h3 := card_sec_mul (V := V) (W := ⊤) (U := C) le_top
  rw [Subgroup.card_top] at h3
  have hC : 0 < Nat.card ↥C := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hC
  calc Nat.card (Sec ⊤ C) * Nat.card ↥C = Nat.card V := h3
    _ ≤ Nat.card ↥A * Nat.card ↥(fixV A) := hcard
    _ ≤ Nat.card ↥A * (Nat.card ↥(fixV (autSec A ⊤ C)) * Nat.card ↥C) :=
        Nat.mul_le_mul_left _ h2
    _ = Nat.card ↥(autSec A ⊤ C) * Nat.card ↥(fixV (autSec A ⊤ C)) * Nat.card ↥C := by
        rw [h1]
        ring

end Abstract

section Params

variable {V : Type} [CommGroup V] {C : Subgroup V}

@[expose] noncomputable def secMk (C : Subgroup V) : V →* Sec ⊤ C :=
  (QuotientGroup.mk' (C.subgroupOf ⊤)).comp Subgroup.topEquiv.symm.toMonoidHom

theorem secMk_surjective (C : Subgroup V) : Function.Surjective (secMk C) := by
  intro y
  obtain ⟨⟨v, hv⟩, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨v, rfl⟩

theorem secHom_secMk (g : ↥(stabSub ⊤ ⊓ stabSub C)) (v : V) :
    secHom ⊤ C g (secMk C v) = secMk C ((g : MulAut V) v) := rfl

theorem commIter_autSec_le {A : Subgroup (MulAut V)} (hA : A ≤ stabSub ⊤ ⊓ stabSub C) (n : ℕ) :
    commIter ⊤ (autSec A ⊤ C) n ≤ (commIter ⊤ A n).map (secMk C) := by
  induction n with
  | zero =>
    show (⊤ : Subgroup (Sec ⊤ C)) ≤ (⊤ : Subgroup V).map (secMk C)
    rw [Subgroup.map_top_of_surjective _ (secMk_surjective C)]
  | succ n ih =>
    show commSub (commIter ⊤ (autSec A ⊤ C) n) (autSec A ⊤ C) ≤
      (commSub (commIter ⊤ A n) A).map (secMk C)
    refine (commSub_mono ih le_rfl).trans ?_
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨a', ha', _, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨g, hgA, rfl⟩ := (mem_autSec_iff_secHom hA).1 ha'
    refine ⟨(g : MulAut V) y * y⁻¹, Subgroup.subset_closure ⟨g, hgA, y, hy, rfl⟩, ?_⟩
    rw [map_mul, map_inv, ← secHom_secMk]

theorem commSeries_autSec_eq_bot {A : Subgroup (MulAut V)} (hA : A ≤ stabSub ⊤ ⊓ stabSub C)
    {k : ℕ} (h : commSeries A k = ⊥) : commSeries (autSec A ⊤ C) k = ⊥ := by
  have := commIter_autSec_le hA k
  rw [show commIter ⊤ A k = commSeries A k from rfl, h, Subgroup.map_bot] at this
  exact le_bot_iff.1 this

variable [Finite V]

theorem rkIdx_fixV_autSec_le (hV : ∀ v : V, v ^ 2 = 1) (A : Subgroup (MulAut V)) :
    rkIdx (fixV (autSec A ⊤ C)) ≤ rkIdx (fixV A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by simpa using hV v⟩
  have hS2 : IsPGroup 2 (Sec ⊤ C) := fun s => ⟨1, by simpa using sec_sq_eq_one hV ⊤ C s⟩
  obtain ⟨m, hm⟩ := hV2.index (fixV A)
  obtain ⟨m', hm'⟩ := hS2.index (fixV (autSec A ⊤ C))
  have h1 := Subgroup.index_mul_card (fixV A)
  have h2 := Subgroup.index_mul_card (fixV (autSec A ⊤ C))
  have h3 := card_fixV_le_autSec (C := C) A
  have h4 := card_sec_mul (V := V) (W := ⊤) (U := C) le_top
  rw [Subgroup.card_top] at h4
  have hle : 2 ^ m' ≤ 2 ^ m := by
    have hpos : 0 < Nat.card ↥(fixV (autSec A ⊤ C)) * Nat.card ↥C :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc 2 ^ m' * (Nat.card ↥(fixV (autSec A ⊤ C)) * Nat.card ↥C)
        = Nat.card (Sec ⊤ C) * Nat.card ↥C := by rw [← hm', ← mul_assoc, h2]
      _ = Nat.card V := h4
      _ = 2 ^ m * Nat.card ↥(fixV A) := by rw [← hm, h1]
      _ ≤ 2 ^ m * (Nat.card ↥(fixV (autSec A ⊤ C)) * Nat.card ↥C) :=
          Nat.mul_le_mul_left _ h3
  unfold rkIdx
  rw [hm, hm', padicValNat.prime_pow, padicValNat.prime_pow]
  exact (Nat.pow_le_pow_iff_right one_lt_two).1 hle

variable {X : Subgroup (MulAut V)} (hX : X ≤ stabSub C) (hf : X ⊓ centSec ⊤ C = ⊥)

include hX hf

theorem rAV_autSec_le (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)} (hA : IsA2 X A) :
    rAV (autSec A ⊤ C) ≤ rAV A := by
  unfold rAV
  have hrk : rk ↥(autSec A ⊤ C) = rk ↥A := by
    unfold rk
    rw [card_autSec_eq hX hf hA.1]
  rw [hrk]
  have hpos : (0 : ℚ) < rk ↥A := by exact_mod_cast hA.rk_pos
  exact div_le_div_of_nonneg_right (by exact_mod_cast rkIdx_fixV_autSec_le hV A) hpos.le

theorem kq_autSec_le (hV : ∀ v : V, v ^ 2 = 1) (k : ℕ) : kq (autSec X ⊤ C) k ≤ kq X k := by
  by_cases htop : kq X k = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp htop
  rw [← hr]
  obtain ⟨A, hA, hAk, hAr⟩ := kq_le_iff.1 (le_of_eq hr.symm)
  have hAs := stab_of_le hX hA.1
  exact kq_le_iff.2 ⟨autSec A ⊤ C, ⟨autSec_mono hA.1 ⊤ C,
    CFSG.QuasithinUnique.Bridge.autSec_ne_bot hAs (not_le_centSec hf hA.1 hA.2.1),
    CFSG.QuasithinUnique.Bridge.isElemAbelian2_autSec hA.2.2 hAs⟩,
    commSeries_autSec_eq_bot hAs hAk, (rAV_autSec_le hX hf hV hA).trans hAr⟩

theorem qOf_autSec_le (hV : ∀ v : V, v ^ 2 = 1) : qOf (autSec X ⊤ C) ≤ qOf X :=
  kq_autSec_le hX hf hV 2

theorem qhatOf_autSec_le (hV : ∀ v : V, v ^ 2 = 1) : qhatOf (autSec X ⊤ C) ≤ qhatOf X :=
  kq_autSec_le hX hf hV 3

end Params

namespace QSec

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)} {C : Subgroup V}
  (h : QSec X K C)

include h

theorem isFFModule_autSec (hFF : IsFFModule X) : IsFFModule (autSec X ⊤ C) :=
  isFFModule_autSec_of_faithful h.stab h.inf_centSec_eq_bot hFF

theorem not_isFFModule (hnot : ¬ IsFFModule (autSec X ⊤ C)) : ¬ IsFFModule X :=
  fun hFF => hnot (h.isFFModule_autSec hFF)

theorem qOf_autSec_le (hV : ∀ v : V, v ^ 2 = 1) : qOf (autSec X ⊤ C) ≤ qOf X :=
  InternalSec.qOf_autSec_le h.stab h.inf_centSec_eq_bot hV

theorem qhatOf_autSec_le (hV : ∀ v : V, v ^ 2 = 1) : qhatOf (autSec X ⊤ C) ≤ qhatOf X :=
  InternalSec.qhatOf_autSec_le h.stab h.inf_centSec_eq_bot hV

end QSec

namespace ISec

variable {G : Type} [Group G] [Finite G] {U Y L Cg : Subgroup G} [IsMulCommutative ↥U]
  (h : ISec U Y L Cg)

include h

omit [Finite G] [IsMulCommutative ↥U] in
theorem elem' : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using h.elem v v.2)

theorem isFFModule_sec (hFF : IsFFModule (autOn Y U)) :
    IsFFModule (autSec (autOn Y U) ⊤ (Cg.subgroupOf U)) :=
  h.qsec.isFFModule_autSec hFF

theorem qOf_sec_le : qOf (autSec (autOn Y U) ⊤ (Cg.subgroupOf U)) ≤ qOf (autOn Y U) :=
  h.qsec.qOf_autSec_le h.elem'

theorem qhatOf_sec_le : qhatOf (autSec (autOn Y U) ⊤ (Cg.subgroupOf U)) ≤ qhatOf (autOn Y U) :=
  h.qsec.qhatOf_autSec_le h.elem'

end ISec

end CFSG.Quasithin.InternalSec
