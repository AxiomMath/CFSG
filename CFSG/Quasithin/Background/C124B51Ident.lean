module

public import CFSG.Quasithin.Background.B5NonId

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace B5

@[expose] def B51IdentBelow (N : ℕ) : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], Nat.card V < N → (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B51Hyp G L → commV L ∉ IrrPlus L ⊤ → IsL345Type ↥L

section Ident

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)} {W U : Subgroup V}

theorem nonirr_identify_below (hA21 : AsA21SQTKSection) (hB42 : AsB42)
    (hA36 : AsA36NoOddCover) (hIH : B51IdentBelow (Nat.card V))
    (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (hU : commV L ∉ IrrPlus L ⊤) :
    IsL345Type ↥L := by
  classical
  obtain ⟨A₀, hA₀⟩ := exists_offender h
  obtain ⟨A, hA, -⟩ := B1Red.exists_isFFStarMin_below hA₀
  have hAG : A ≤ G := hA.1.1
  have hAel : IsElemAbelian2 A := hA.1.2.2.1
  have hAne : A ≠ ⊥ := hA.1.2.1
  have hA2 : IsPGroup 2 A := hAel.isPGroup
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
  have hlt₂ : Y₂ < W₂ := by
    refine lt_of_le_of_ne hY₂W₂ fun heq => hnc₂ ?_
    exact (commSub_le_of_invariant (fun x hx w hw =>
      (hMW₂ (Subgroup.mem_sup_left hx) w).2 hw)).trans heq.symm.le
  have c₂ : SecCtx G L A W₂ Y₂ := ⟨hAG, hAel, hAne, hY₂W₂, hMW₂, hMY₂, hnc₂⟩
  have hAI : A ≤ stabSub I := le_sup_right.trans hMI
  have hAW₂ : A ≤ stabSub W₂ := le_sup_right.trans hMW₂
  have hAY₂ : A ≤ stabSub Y₂ := le_sup_right.trans hMY₂
  have hAY : A ≤ stabSub Y := le_sup_right.trans hMY
  have hsum := rAV_add_le_one hV hA.1 (inf_le_left : Y ≤ I) hIY₂ hY₂W₂ hAI hAW₂ hAY₂ hAY
    (sec_A_inf_centSec h c₁) (sec_A_inf_centSec h c₂)
  have hq₁ := qOf_secX_le h c₁ hquad
  have hq₂ := qOf_secX_le h c₂ hquad
  have hMG : IsFFStarOffender (L ⊔ A) A := ⟨le_sup_right, hAne, hAel, hA.1.2.2.2⟩
  have hFs : quasithinGenFitting (L ⊔ A) = L := genFitting_sup_eq h hAG hA2
  have hq₀ : CFSG.IsQuasisimple ↥(quasithinGenFitting (L ⊔ A)) := by rw [hFs]; exact quasi_L h
  have hO2 : pCoreOf 2 (L ⊔ A) = ⊥ := pCoreOf_sup_eq_bot h hAG hA2
  by_cases hr₁ : rAV (autSec A I Y) ≤ 1 / 2
  ·
    obtain ⟨-, ⟨B, -, hB⟩, -⟩ := B1_5_8 hV hMG (W := I) (U := Y) inf_le_left hMI hMY hq₀ hO2
      (by rw [hFs]; exact hnc₁)
    have hirr := isIrrSec_autSec hIlt hIirr (le_sup_left.trans hMI) (le_sup_left.trans hMY)
    exact isL345_lift hA36 h c₁ (isL345_of_irr hA21 hB42 hV h c₁ hirr hB
      (hq₁.trans (WithTop.coe_le_coe.2 hr₁)))
  · have hr₂ : rAV (autSec A W₂ Y₂) ≤ 1 / 2 := by
      by_contra hcon
      push Not at hr₁ hcon
      linarith
    obtain ⟨-, ⟨B, -, hB⟩, -⟩ := B1_5_8 hV hMG (W := W₂) (U := Y₂) hY₂W₂ hMW₂ hMY₂ hq₀ hO2
      (by rw [hFs]; exact hnc₂)
    have hirrX := isIrrSec_secX c₂ hlt₂ hch
    have hq₂' : qOf (autSec (L ⊔ A) W₂ Y₂) ≤ ((1 / 2 : ℚ) : WithTop ℚ) :=
      hq₂.trans (WithTop.coe_le_coe.2 hr₂)
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
    have hHyp := b51Hyp_secY h c₂ hA21 hB
    refine isL345_lift hA36 h c₂ ?_
    by_cases hi : commV (autSec L W₂ Y₂) ∈ IrrPlus (autSec L W₂ Y₂) ⊤
    · exact isL345_of_irr hA21 hB42 hV h c₂ (isIrrSec_secL_of_irrPlus h c₂ hirrX hi) hB hq₂'
    · exact hIH (Sec W₂ Y₂) hcard (sq_eq_one_sec hV W₂ Y₂) _ _ hHyp hi

theorem b51IdentBelow (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hA36 : AsA36NoOddCover) :
    ∀ N, B51IdentBelow N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro V _ _ hVN hV G L h hU
    exact nonirr_identify_below hA21 hB42 hA36 (ih (Nat.card V) hVN) hV h hU

theorem b51_ident (hA21 : AsA21SQTKSection) (hB42 : AsB42) (hA36 : AsA36NoOddCover)
    (hV : ∀ v : V, v ^ 2 = 1) (h : B51Hyp G L) (hU : commV L ∉ IrrPlus L ⊤) :
    IsL345Type ↥L :=
  b51IdentBelow hA21 hB42 hA36 (Nat.card V + 1) V (Nat.lt_succ_self _) hV G L h hU

end Ident

end B5

end CFSG.Quasithin
