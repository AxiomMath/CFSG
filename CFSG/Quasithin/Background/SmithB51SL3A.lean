module

public import CFSG.Quasithin.Background.SmithB51SL3Common

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace B5

theorem card_statedSL_three_eq (K : Type) [Field K] [Fintype K] :
    Nat.card ↥(StatedSL 3 K) =
      Fintype.card K ^ 3 * (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 3 - 1) := by
  rw [CFSG.Open.StatedAPI.card_statedSL_three, Nat.card_eq_fintype_card, mul_assoc]

theorem card_statedSL_four_five {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nat.card ↥(StatedSL 4 K) = 20160 ∧ Nat.card ↥(StatedSL 5 K) = 9999360 := by
  have := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  refine ⟨?_, ?_⟩
  · rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 4 K).toEquiv, Matrix.card_SL_field, hK]
    decide
  · rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 5 K).toEquiv, Matrix.card_SL_field, hK]
    decide

theorem not_nonempty_equiv_sl3_sl45 {K K' : Type} [Field K] [Finite K] [Field K'] [Finite K']
    {n m : ℕ} (hK : Nat.card K = 2 ^ n) (hK' : Nat.card K' = 2) (hm : m = 4 ∨ m = 5) :
    ¬ Nonempty (↥(StatedSL 3 K) ≃* ↥(StatedSL m K')) := by
  rintro ⟨e⟩
  have hc := Nat.card_congr e.toEquiv
  have := Fintype.ofFinite K
  rw [card_statedSL_three_eq, ← Nat.card_eq_fintype_card, hK] at hc
  obtain ⟨h4, h5⟩ := card_statedSL_four_five hK'
  have hne : n ≠ 0 := by
    rintro rfl
    have : (1 : ℕ) < Nat.card K := Finite.one_lt_card
    omega
  have hval : (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) = 20160 ∨
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) = 9999360 := by
    rcases hm with rfl | rfl
    · exact Or.inl (hc.trans h4)
    · exact Or.inr (hc.trans h5)
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n <;> norm_num at hval
  · have h8 : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    set q := 2 ^ n
    have hq2' : 64 ≤ q ^ 2 := by
      calc 64 = 8 * 8 := by norm_num
        _ ≤ q * q := Nat.mul_le_mul h8 h8
        _ = q ^ 2 := (sq q).symm
    have hq3' : 512 ≤ q ^ 3 := by
      calc 512 = 8 * 8 * 8 := by norm_num
        _ ≤ q * q * q := Nat.mul_le_mul (Nat.mul_le_mul h8 h8) h8
        _ = q ^ 3 := by ring
    have hq2 : 63 ≤ q ^ 2 - 1 := by omega
    have hq3 : 511 ≤ q ^ 3 - 1 := by omega
    have : 512 * 63 * 511 ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul hq3' hq2) hq3
    rcases hval with hval | hval <;> omega

section Ident

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

structure SL3Data (G L : Subgroup (MulAut V)) : Type where
  A : Subgroup (MulAut V)
  I : Subgroup V
  Y₂ : Subgroup V
  W₂ : Subgroup V
  hmin : IsFFStarMin G A
  hAL : A ≤ L
  hquad : IsQuadratic A
  hI : I ∈ IrrPlus L ⊤
  hIY₂ : I ≤ Y₂
  hY₂W₂ : Y₂ ≤ W₂
  hLI : L ≤ stabSub I
  hLY : L ≤ stabSub (I ⊓ fixV L)
  hLY₂ : L ≤ stabSub Y₂
  hLW₂ : L ≤ stabSub W₂
  hnc : ¬ commSub W₂ L ≤ Y₂
  hch : ∀ X : Subgroup V, L ≤ stabSub X → Y₂ ≤ X → X ≤ W₂ → X = Y₂ ∨ X = W₂
  hf₁ : L ⊓ centSec I (I ⊓ fixV L) = ⊥
  hf₂ : L ⊓ centSec W₂ Y₂ = ⊥
  hnat₁ : ∃ n, BinaryNaturalSL (autSec L I (I ⊓ fixV L)) ⊤ ⊥ 3 n
  hnat₂ : ∃ n, BinaryNaturalSL (autSec L W₂ Y₂) ⊤ ⊥ 3 n
  hr₁ : 2 * rkIdx (fixV (autSec A I (I ⊓ fixV L))) = rk A
  hr₂ : 2 * rkIdx (fixV (autSec A W₂ Y₂)) = rk A

theorem false_of_sec_sl45 (hA36 : AsA36NoOddCover) (h : B51Hyp G L) {A : Subgroup (MulAut V)}
    {W U : Subgroup V} (c : SecCtx G L A W U) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (eL : ↥L ≃* ↥(StatedSL 3 K)) {K' : Type} [Field K'] [Finite K']
    (hK' : Nat.card K' = 2) {m : ℕ} (hm : m = 4 ∨ m = 5)
    (e : ↥(StatedSL m K') ≃* ↥(autSec L W U)) : False := by
  have hT : IsL345Type ↥(autSec L W U) := by
    rcases hm with rfl | rfl
    · exact Or.inr (Or.inl ⟨K', inferInstance, inferInstance, hK', ⟨e.symm⟩⟩)
    · exact Or.inr (Or.inr ⟨K', inferInstance, inferInstance, hK', ⟨e.symm⟩⟩)
  have hfaith := sec_faithful hA36 h c hT
  have hfL : L ⊓ centSec W U = ⊥ := by
    rw [eq_bot_iff, ← hfaith]
    exact inf_le_inf_right _ le_sup_left
  let eS := secEquiv L (le_sup_left.trans c.hMW) (le_sup_left.trans c.hMU) hfL
  exact not_nonempty_equiv_sl3_sl45 hK hK' hm ⟨(eL.symm.trans eS).trans e.symm⟩

theorem false_of_b42Case9 (hA36 : AsA36NoOddCover) (h : B51Hyp G L) {A : Subgroup (MulAut V)}
    {W U : Subgroup V} (c : SecCtx G L A W U) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (eL : ↥L ≃* ↥(StatedSL 3 K))
    (h9 : B42Case9 (autSec (L ⊔ A) W U) (autSec L W U)) : False := by
  obtain ⟨-, m, hm, hnat, -⟩ := h9
  obtain ⟨K', hK'f, hK'fin, hK', ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hnat
  exact false_of_sec_sl45 hA36 h c hK eL (by simpa using hK') hm e

theorem false_of_case_iii_iv (hA36 : AsA36NoOddCover) (h : B51Hyp G L) {A : Subgroup (MulAut V)}
    {W U : Subgroup V} (c : SecCtx G L A W U) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (eL : ↥L ≃* ↥(StatedSL 3 K)) {Y : Subgroup (MulAut (Sec W U))}
    (hc : (∃ k, B51Case1iii Y (autSec L W U) k) ∨ B51Case1iv Y (autSec L W U)) : False := by
  rcases hc with ⟨k, -, hk, π, U₁, U₂, -, hr1, -⟩ | ⟨-, k, hk, j, hj1, -, I', π, -, -, -, hreal⟩
  · have hbij : Function.Bijective π :=
      ⟨realizesVia_injective (FFModel.nat_faithful _) hr1, hr1.1⟩
    exact false_of_sec_sl45 hA36 h c hK eL (Nat.card_zmod 2) hk (MulEquiv.ofBijective π hbij)
  · have hr1 := hreal ⟨0, hj1⟩
    have hbij : Function.Bijective π :=
      ⟨realizesVia_injective (FFModel.nat_faithful _) hr1, hr1.1⟩
    exact false_of_sec_sl45 hA36 h c hK eL (Nat.card_zmod 2) hk (MulEquiv.ofBijective π hbij)

theorem sl3_sections (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hA36 : AsA36NoOddCover)
    (hIH : B51Part1Below (Nat.card V)) (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L)
    (hU : commV L ∉ IrrPlus L ⊤) {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (eL : ↥L ≃* ↥(StatedSL 3 K)) : Nonempty (SL3Data G L) := by
  classical
  obtain ⟨A₀, hA₀⟩ := exists_offender h
  obtain ⟨A, hA, -⟩ := B1Red.exists_isFFStarMin_below hA₀
  have hAG : A ≤ G := hA.1.1
  have hAel : IsElemAbelian2 A := hA.1.2.2.1
  have hAne : A ≠ ⊥ := hA.1.2.1
  have hquad : IsQuadratic A := B1_4_3 hV hA
  obtain ⟨I, Y₂, W₂, hI, hMI, hIY₂, hY₂W₂, hMY₂, hMW₂, hnc₂, hch⟩ := exists_chief_pair hV h hU hA
  obtain ⟨hIL, hIcomm, hIlt, hIirr⟩ := irr_data hI
  set Y := I ⊓ fixV L with hYdef
  have hAn : ∀ a ∈ A, ∀ x ∈ L, a * x * a⁻¹ ∈ L := fun a ha x hx => normal_L h a (hAG ha) x hx
  have hIA : ∀ a ∈ A, ∀ w ∈ I, a w ∈ I := fun a ha w hw =>
    (hMI (Subgroup.mem_sup_right ha) w).2 hw
  have hMY : L ⊔ A ≤ stabSub Y := by
    refine sup_le_stabSub (fun x hx w hw => ?_) (fun a ha w hw => ?_)
    · have : x w = w := hw.2 x hx
      rw [this]; exact hw
    · exact ⟨hIA a ha w hw.1, B1Red.fixV_inv_of_normalizes hAn a ha w hw.2⟩
  have hnc₁ : ¬ commSub I L ≤ Y := by
    rw [hIcomm]
    intro hle
    exact lt_irrefl _ (lt_of_lt_of_le hIlt hle)
  have c₁ : SecCtx G L A I Y := ⟨hAG, hAel, hAne, inf_le_left, hMI, hMY, hnc₁⟩
  have c₂ : SecCtx G L A W₂ Y₂ := ⟨hAG, hAel, hAne, hY₂W₂, hMW₂, hMY₂, hnc₂⟩
  have hAI : A ≤ stabSub I := le_sup_right.trans hMI
  have hAW₂ : A ≤ stabSub W₂ := le_sup_right.trans hMW₂
  have hAY₂ : A ≤ stabSub Y₂ := le_sup_right.trans hMY₂
  have hAY : A ≤ stabSub Y := le_sup_right.trans hMY
  have hsum := rAV_add_le_one hV hA.1 (inf_le_left : Y ≤ I) hIY₂ hY₂W₂ hAI hAW₂ hAY₂ hAY
    (sec_A_inf_centSec h c₁) (sec_A_inf_centSec h c₂)
  have hq₁ := qOf_secX_le h c₁ hquad
  have hq₂ := qOf_secX_le h c₂ hquad
  have hirr₁ := isIrrSec_autSec hIlt hIirr (le_sup_left.trans hMI) (le_sup_left.trans hMY)
  have hcard : Nat.card (Sec W₂ Y₂) < Nat.card V := by
    have h1 := card_sec_mul hY₂W₂
    have h2 : Nat.card W₂ ≤ Nat.card V := Subgroup.card_le_card_group W₂
    have h3 : Nat.card I ≤ Nat.card Y₂ := Subgroup.card_le_of_le hIY₂
    have hIne : I ≠ ⊥ := by
      rintro rfl
      exact not_lt_bot hIlt
    have h4 : 1 < Nat.card I := (Subgroup.one_lt_card_iff_ne_bot I).2 hIne
    have h5 : 0 < Nat.card (Sec W₂ Y₂) := Nat.card_pos
    nlinarith
  have hr₁0 : (0 : ℚ) ≤ rAV (autSec A I Y) := by unfold rAV; positivity
  have hr₂0 : (0 : ℚ) ≤ rAV (autSec A W₂ Y₂) := by unfold rAV; positivity
  have hqr : ∀ {W U : Subgroup V} (c : SecCtx G L A W U) {r : ℚ},
      qOf (autSec (L ⊔ A) W U) = ((r : ℚ) : WithTop ℚ) → r ≤ rAV (autSec A W U) := by
    intro W U c r hr
    have := qOf_secX_le h c hquad
    rw [hr] at this
    exact_mod_cast this
  have hqr' : ∀ {W U : Subgroup V} (c : SecCtx G L A W U),
      ((2 / 3 : ℚ) : WithTop ℚ) ≤ qOf (autSec (L ⊔ A) W U) → 2 / 3 ≤ rAV (autSec A W U) := by
    intro W U c hle
    have := hle.trans (qOf_secX_le h c hquad)
    exact_mod_cast this
  have hS₂ : rAV (autSec A W₂ Y₂) < 1 →
      1 / 2 ≤ rAV (autSec A W₂ Y₂) ∧
        (rAV (autSec A W₂ Y₂) < 2 / 3 →
          B42Case2 (autSec (L ⊔ A) W₂ Y₂) (autSec L W₂ Y₂)) := by
    intro hlt
    obtain ⟨B₂, -, hB₂, -, hcase⟩ := sec_cases_IH hA21 hIH hV h c₂ hquad hcard hch hlt
    rcases hcase with hirr₂ | hc
    · rcases b42_trichotomy hA21 hB42 hV h c₂ hirr₂ hB₂ with h2 | h9 | hbig
      · exact ⟨hqr c₂ h2.2.2, fun _ => h2⟩
      · exact (false_of_b42Case9 hA36 h c₂ hK eL h9).elim
      · have := hqr' c₂ hbig
        exact ⟨by linarith, fun hlt' => absurd this (not_le.2 hlt')⟩
    · exact (false_of_case_iii_iv hA36 h c₂ hK eL hc).elim
  obtain ⟨B₁, -, hB₁, -⟩ := exists_offender_max (sq_eq_one_sec hV I Y) (isA2_secA h c₁)
    (by linarith)
  have h2₁ : B42Case2 (autSec (L ⊔ A) I Y) (autSec L I Y) := by
    rcases b42_trichotomy hA21 hB42 hV h c₁ hirr₁ hB₁ with h2 | h9 | hbig
    · exact h2
    · exact (false_of_b42Case9 hA36 h c₁ hK eL h9).elim
    · exfalso
      have h1 := hqr' c₁ hbig
      have h2 := (hS₂ (by linarith)).1
      linarith
  have hr₁ : 1 / 2 ≤ rAV (autSec A I Y) := hqr c₁ h2₁.2.2
  obtain ⟨hr₂, h2₂'⟩ := hS₂ (by linarith)
  have hr₁e : rAV (autSec A I Y) = 1 / 2 := by linarith
  have hr₂e : rAV (autSec A W₂ Y₂) = 1 / 2 := by linarith
  have h2₂ := h2₂' (by linarith)
  have hT : ∀ {W U : Subgroup V}, B42Case2 (autSec (L ⊔ A) W U) (autSec L W U) →
      IsL345Type ↥(autSec L W U) := by
    intro W U h2
    obtain ⟨-, ⟨m, hm⟩, -⟩ := h2
    obtain ⟨K', hK'f, hK'fin, hK', ⟨e⟩⟩ := BinaryNaturalSL.exists_equiv hm
    exact Or.inl ⟨m, K', hK'f, hK'fin, hK', ⟨e.symm⟩⟩
  have hfaith₁ := sec_faithful hA36 h c₁ (hT h2₁)
  have hfaith₂ := sec_faithful hA36 h c₂ (hT h2₂)
  have hAL : A ≤ L := le_L_of_ffJ_eq hV h c₁ hquad hfaith₁ h2₁.1
    (by rw [h2₁.2.2, hr₁e]) (by rw [hr₁e]; norm_num)
  have hLA : L ⊔ A = L := sup_eq_left.2 hAL
  have hrk : ∀ {W U : Subgroup V} (c : SecCtx G L A W U), rAV (autSec A W U) = 1 / 2 →
      2 * rkIdx (fixV (autSec A W U)) = rk A := by
    intro W U c he
    have hpos : 0 < rk (autSec A W U) := (isA2_secA h c).rk_pos
    have heq : rk (autSec A W U) = rk A :=
      rk_autSec_eq (le_sup_right.trans c.hMW) (le_sup_right.trans c.hMU) (sec_A_inf_centSec h c)
    unfold rAV at he
    rw [div_eq_iff (by exact_mod_cast hpos.ne')] at he
    have : (2 * rkIdx (fixV (autSec A W U)) : ℚ) = (rk (autSec A W U) : ℚ) := by linarith
    rw [← heq]
    exact_mod_cast this
  have hf₁ : L ⊓ centSec I Y = ⊥ := by
    rw [eq_bot_iff, ← hfaith₁]
    exact inf_le_inf_right _ le_sup_left
  have hf₂ : L ⊓ centSec W₂ Y₂ = ⊥ := by
    rw [eq_bot_iff, ← hfaith₂]
    exact inf_le_inf_right _ le_sup_left
  exact ⟨⟨A, I, Y₂, W₂, hA, hAL, hquad, hI, hIY₂, hY₂W₂, le_sup_left.trans hMI,
    le_sup_left.trans hMY, le_sup_left.trans hMY₂, le_sup_left.trans hMW₂, hnc₂,
    fun X hX => hch X (by rw [hLA]; exact hX), hf₁, hf₂, h2₁.2.1, h2₂.2.1, hrk c₁ hr₁e,
    hrk c₂ hr₂e⟩⟩

end Ident

end B5

end CFSG.Quasithin
