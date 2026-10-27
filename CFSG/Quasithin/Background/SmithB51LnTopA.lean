module

public import CFSG.Quasithin.Background.SmithB51LnChief
public import CFSG.Quasithin.Background.SmithB51LnSum

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}

theorem top_first (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hIH : B51Part1Below (Nat.card V))
    (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (hU : commV L ∉ IrrPlus L ⊤) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (eL : ↥L ≃* ↥(StatedSL n (ZMod 2))) {A : Subgroup (MulAut V)}
    (hA : IsFFStarMin G A) :
    A ≤ L ∧ ∃ (I : Subgroup V) (π₁ : ↥(StatedSL n (ZMod 2)) →* ↥L),
      I ∈ IrrPlus L ⊤ ∧ (L ⊔ A ≤ stabSub I) ∧ RealM L I (I ⊓ fixV L) π₁ mat := by
  classical
  have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_equiv (Nat.card_zmod 2) eL
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
  have hr₂ := chief_sec_lower hA21 hB42 hIH hV h c₂ hquad hcard hch hZ hn eL (by linarith)
  have hirr₁ := isIrrSec_autSec hIlt hIirr (le_sup_left.trans hMI) (le_sup_left.trans hMY)
  rcases irr_sec_cases hA21 hB42 hV h c₁ hquad hirr₁ hZ hn eL (by linarith) with
    ⟨⟨π', hπ'⟩, -⟩ | ⟨h34, h5⟩
  · have hR := RealM.ofSec (le_sup_left.trans hMI) (le_sup_left.trans hMY) (faithful_secL h c₁ hZ)
      hπ'
    rw [secPre_top, secPre_bot inf_le_left] at hR
    refine ⟨fun a ha => ?_, I, _, hI, hMI, hR⟩
    have haG := hAG ha
    obtain ⟨l, hl, hinner⟩ :=
      hR.exists_inner (Or.inl rfl) (by rcases hn with rfl | rfl <;> norm_num)
      (g := a) (normal_L h a haG) (fun x hx => by
        have := normal_L h a⁻¹ (G.inv_mem haG) x hx
        simpa using this) (hMI (Subgroup.mem_sup_right ha)) (hMY (Subgroup.mem_sup_right ha))
    exact mem_of_inner h haG (hAel.2 a ha) hl hinner
  · exfalso
    rcases hn with rfl | rfl
    · norm_num at hr₂
      linarith
    · have := h5 rfl
      norm_num at hr₂
      linarith

end CFSG.Quasithin.B5.Ln
