module

public import CFSG.Quasithin.Background.SmithB51LnSub

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique Matrix Module
open scoped Matrix

theorem eq_of_equiv_sl {m n : ℕ} (hm : m = 4 ∨ m = 5) (hn : n = 4 ∨ n = 5)
    (e : ↥(StatedSL m (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2))) : m = n := by
  have h := Nat.card_congr e.toEquiv
  rcases hm with rfl | rfl <;> rcases hn with rfl | rfl
  · rfl
  · rw [card_statedSL_four, card_statedSL_five] at h; omega
  · rw [card_statedSL_four, card_statedSL_five] at h; omega
  · rfl

theorem realM_of_binaryNat {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {m n : ℕ} (hm : m = 4 ∨ m = 5) (hn : n = 4 ∨ n = 5) (e : ↥H ≃* ↥(StatedSL n (ZMod 2)))
    (h : BinaryNaturalSL H U Z m 1) :
    ∃ π : ↥(StatedSL n (ZMod 2)) →* ↥H, RealM H U Z π mat := by
  obtain ⟨π, hπ⟩ := realM_of_binaryNaturalSL h
  have hbij : Function.Bijective π := ⟨hπ.injective (Or.inl rfl), hπ.1⟩
  have hmn := eq_of_equiv_sl hm hn ((MulEquiv.ofBijective π hbij).trans e)
  subst hmn
  exact ⟨π, hπ⟩

theorem eq_of_binaryNat {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {m n : ℕ} (hm : m = 4 ∨ m = 5) (hn : n = 4 ∨ n = 5) (e : ↥H ≃* ↥(StatedSL n (ZMod 2)))
    (h : BinaryNaturalSL H U Z m 1) : m = n := by
  obtain ⟨π, hπ⟩ := realM_of_binaryNaturalSL h
  have hbij : Function.Bijective π := ⟨hπ.injective (Or.inl rfl), hπ.1⟩
  exact eq_of_equiv_sl hm hn ((MulEquiv.ofBijective π hbij).trans e)

theorem one_div_le_rAV {V : Type} [CommGroup V] [Finite V] {L : Subgroup (MulAut V)}
    {X : Subgroup V} {n : ℕ} {π : ↥(StatedSL n (ZMod 2)) →* ↥L}
    {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)} (h : RealM L X ⊥ π M)
    (hM : M = mat ∨ M = dmat) (hn : 2 ≤ n) {B : Subgroup (MulAut V)} (hBL : B ≤ L)
    (hB2 : IsPGroup 2 ↥B) (hBne : B ≠ ⊥) : (1 / ((n : ℚ) - 1)) ≤ rAV B := by
  obtain ⟨h1, h2⟩ := h.rk_le hM hBL hB2 hBne (by omega)
  have h3 : rkIdx (fixV (autSec B X ⊥)) ≤ rkIdx (fixV B) := by
    rw [rkIdx_fixV_autSec_bot (hBL.trans h.hLW), ← rkSub_top]
    exact rkSub_mono le_top
  have hpos : 0 < rk B := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hBne ((rk_eq_zero_iff_of_isPGroup hB2).1 h0)
  unfold rAV
  have hn1 : (0 : ℚ) < (n : ℚ) - 1 := by
    have : (2 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  rw [div_le_div_iff₀ hn1 (by exact_mod_cast hpos), one_mul]
  have h4 : (rk B : ℚ) ≤ ((n - 1 : ℕ) : ℚ) * (rkIdx (fixV B) : ℚ) := by
    exact_mod_cast h1.trans (Nat.mul_le_mul_left _ h3)
  have h5 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [h5] at h4
  linarith

section Sec

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)} {W Y : Subgroup V}

@[expose] noncomputable def secEquivSL (h : B51Hyp G L) (c : SecCtx G L A W Y)
    (hZ : Subgroup.center ↥L = ⊥) {n : ℕ} (eL : ↥L ≃* ↥(StatedSL n (ZMod 2))) :
    ↥(autSec L W Y) ≃* ↥(StatedSL n (ZMod 2)) :=
  (B5.secEquiv L (le_sup_left.trans c.hMW) (le_sup_left.trans c.hMU)
    (faithful_secL h c hZ)).symm.trans eL

theorem irr_sec_cases (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hV : ∀ v : V, v ^ 2 = 1)
    (h : B51Hyp G L) (c : SecCtx G L A W Y) (hquad : IsQuadratic A)
    (hirr : XMod.IsIrrSec ↥(autSec L W Y) (⊥ : Subgroup (Sec W Y)) ⊤)
    (hZ : Subgroup.center ↥L = ⊥) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (eL : ↥L ≃* ↥(StatedSL n (ZMod 2))) (hr : rAV (autSec A W Y) ≤ 1) :
    ((∃ π : ↥(StatedSL n (ZMod 2)) →* ↥(autSec L W Y), RealM (autSec L W Y) ⊤ ⊥ π mat) ∧
        (1 / ((n : ℚ) - 1)) ≤ rAV (autSec A W Y)) ∨
      ((3 / 4 : ℚ) ≤ rAV (autSec A W Y) ∧ (n = 5 → (1 : ℚ) ≤ rAV (autSec A W Y))) := by
  obtain ⟨B, -, hB, -⟩ := exists_offender_max (CFSG.Quasithin.sq_eq_one_sec hV W Y)
    (isA2_secA h c) hr
  have hc := hB42 (Sec W Y) (CFSG.Quasithin.sq_eq_one_sec hV W Y) _ _ (b4Hyp_sec' h c hA21 hirr)
    B hB
  have hq := qOf_secX_le h c hquad
  rcases b42_ln (b4Hyp_sec' h c hA21 hirr) hB hc hn (secEquivSL h c hZ eL) with h9 | ⟨h34, h5⟩
  · obtain ⟨-, m, hm, hnat, hq9⟩ := h9
    have hmn := eq_of_binaryNat hm hn (secEquivSL h c hZ eL) hnat
    subst hmn
    refine Or.inl ⟨realM_of_binaryNat hm hm (secEquivSL h c hZ eL) hnat, ?_⟩
    rw [hq9] at hq
    exact_mod_cast hq
  · right
    refine ⟨?_, fun h5' => ?_⟩
    · have := h34.trans hq
      exact_mod_cast this
    · have := (h5 h5').trans hq
      exact_mod_cast this

theorem chief_sec_lower (hA21 : AsA21SQTKSection) (hB42 : AsB42)
    (hIH : B51Part1Below (Nat.card V)) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (c : SecCtx G L A W Y) (hquad : IsQuadratic A) (hcard : Nat.card (Sec W Y) < Nat.card V)
    (hch : ∀ X : Subgroup V, L ⊔ A ≤ stabSub X → Y ≤ X → X ≤ W → X = Y ∨ X = W)
    (hZ : Subgroup.center ↥L = ⊥) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (eL : ↥L ≃* ↥(StatedSL n (ZMod 2))) (hr : rAV (autSec A W Y) ≤ 1) :
    (1 / ((n : ℚ) - 1)) ≤ rAV (autSec A W Y) := by
  have hS2 := CFSG.Quasithin.sq_eq_one_sec hV W Y
  obtain ⟨B, hBA, hB, hBc, -, hcase⟩ := sec_IH hA21 hIH hV h c hcard hr
  have hlt : Y < W := by
    refine lt_of_le_of_ne c.hUW fun heq => c.hnc ?_
    exact (commSub_le_of_invariant (fun x hx w hw =>
      (c.hMW (Subgroup.mem_sup_left hx) w).2 hw)).trans heq.symm.le
  set eS := secEquivSL h c hZ eL with heS
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hρ : (1 / ((n : ℚ) - 1)) ≤ 1 := by
    have : (2 : ℚ) ≤ n := by exact_mod_cast hn2
    rw [div_le_one (by linarith)]
    linarith
  have hB2 : IsPGroup 2 ↥B := hB.2.2.1.isPGroup
  have transfer : (1 / ((n : ℚ) - 1)) ≤ rAV B → (1 / ((n : ℚ) - 1)) ≤ rAV (autSec A W Y) :=
    fun hB' => le_rAV_of_card_le hS2 hBA (isA2_secA h c).2.2 hB.2.1 hBc hρ hB'
  rcases hcase with hi | hii | ⟨m, hGeq, hm, π, U₁, U₂, -, h1, -⟩ |
    ⟨hGeq, m, hm, k, hk1, -, I, π, -, -, -, hreal⟩
  · have hirr := isIrrSec_secL_of_irrPlus h c (isIrrSec_secX c hlt hch) hi.1
    rcases irr_sec_cases hA21 hB42 hV h c hquad hirr hZ hn eL hr with ⟨-, hlow⟩ | ⟨h34, h5⟩
    · exact hlow
    · refine le_trans ?_ h34
      rcases hn with rfl | rfl <;> norm_num
  · exact absurd hii (not_b51Case1ii hn eS)
  · have hBL : B ≤ autSec L W Y := le_sup_right.trans hGeq.le
    have hR := realM_mat_iff.2 h1
    have hbij : Function.Bijective π := ⟨hR.injective (Or.inl rfl), hR.1⟩
    have hmn := eq_of_equiv_sl hm hn ((MulEquiv.ofBijective π hbij).trans eS)
    subst hmn
    exact transfer (one_div_le_rAV hR (Or.inl rfl) hn2 hBL hB2 hB.2.1)
  · have hBL : B ≤ autSec L W Y := le_sup_right.trans hGeq.le
    have hR := realM_mat_iff.2 (hreal ⟨0, hk1⟩)
    have hbij : Function.Bijective π := ⟨hR.injective (Or.inl rfl), hR.1⟩
    have hmn := eq_of_equiv_sl hm hn ((MulEquiv.ofBijective π hbij).trans eS)
    subst hmn
    exact transfer (one_div_le_rAV hR (Or.inl rfl) hn2 hBL hB2 hB.2.1)

end Sec

end CFSG.Quasithin.B5.Ln
