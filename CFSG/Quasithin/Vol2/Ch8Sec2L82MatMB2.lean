module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TMB2
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB2T
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR3
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB2R1
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB2R2
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB2R3
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB2R4
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR2L
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR4L

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Code22 CFSG.Quasithin.H.LU
  CFSG.Quasithin.H.LU24 CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H.L34Z
  CFSG.Quasithin.E3 CFSG.Quasithin.H13 CFSG.Quasithin.H13.L828T CFSG.Quasithin.H13.Ch9.Herm9
  CFSG.Quasithin.H.Coc

@[expose] def MB2Field (n : ℕ) (R : Type) [Ring R] : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = n ∧ Nonempty (R ≃+* K)

section Rows

variable {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)}

theorem mb2_row2_data
    (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCode22 H ⊤ ⊥) (hX : rk ↥X = 5) (hfX : rkIdx (fixV X) = 6) :
    ∃ e : V ≃* W10, H.map (congrHom e) = imgC mog22 ∧
      s828BPrime (imgC mog22) (X.map (congrHom e)) = maskSub 10 mb2B9 ∧
      perfectCore (imgC mog22 ⊓ stabSub (fixV (X.map (congrHom e)))) = imgC hbQ ∧
      fixV (X.map (congrHom e)) = UC := by
  have hXc : Nat.card ↥X = 2 ^ 5 := hX ▸ card_eq_of_isElemAbelian2 hXe
  obtain ⟨e, hH, hU, hc1, hc2⟩ := code22_E32_comm_std h hXN (isElemAbelian2_iff.1 hXe) hXc
  have hU' : fixV (X.map (congrHom e)) = UC := hU
  have hB := std2_BPrime_eq (X.map (congrHom e)) hU' hc1 hc2
  exact ⟨e, hH, hB,
    (congrArg (fun U => perfectCore (imgC mog22 ⊓ stabSub U)) hU').trans perfectCore_stab_UC, hU'⟩

theorem mb2_row3_data
    (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCode24 H ⊤ ⊥) (hX : rk ↥X = 6) (hfX : rkIdx (fixV X) = 7) :
    ∃ e : V ≃* W11, H.map (congrHom e) = (rhoC11 AutPerm le_rfl).range ∧
      s828BPrime (rhoC11 AutPerm le_rfl).range (X.map (congrHom e)) = maskSub 11 mb3L10 ∧
      perfectCore ((rhoC11 AutPerm le_rfl).range ⊓ stabSub (fixV (X.map (congrHom e)))) =
        imgCd sxP0 ∧ fixV (X.map (congrHom e)) = US := by
  obtain ⟨e, hH, hU⟩ := row3_classify hXN hXe h hX hfX
  have hS := card_stab_US_le
  have hXN' : X.map (congrHom e) ≤
      Subgroup.normalizer (((rhoC11 AutPerm le_rfl).range : Subgroup (MulAut W11)) :
        Set (MulAut W11)) := by
    have := map_le_normalizer_congrHom e hXN
    rwa [hH] at this
  refine ⟨e, hH, row3_std_B hS _ hXN' hU, ?_, hU⟩
  exact (congrArg (fun U => perfectCore ((rhoC11 AutPerm le_rfl).range ⊓ stabSub U)) hU).trans
    (lu_code_std hS).1

theorem mb2_row4_data
    (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCocode24 H ⊤ ⊥) (hX : rk ↥X = 6) (hfX : rk ↥(fixV X) = 3) :
    ∃ e : V ≃* W11, H.map (congrHom e) = img11 AutPerm ∧
      s828BPrime (img11 AutPerm) (X.map (congrHom e)) = maskSub 11 mb4L9 ∧
      perfectCore (img11 AutPerm ⊓ stabSub (fixV (X.map (congrHom e)))) = img11 trQ ∧
      fixV (X.map (congrHom e)) = UT := by
  obtain ⟨e₀, he₀⟩ := cocode24_std h
  have hV : ∀ v : V, v ^ 2 = 1 := sq_eq_one_of_equiv e₀
  have hXc : Nat.card ↥X = 2 ^ 6 := hX ▸ card_eq_of_isElemAbelian2 hXe
  have hfXc : Nat.card ↥(fixV X) = 2 ^ 3 := hfX ▸ card_eq_two_pow hV (fixV X)
  obtain ⟨g, hXU, hXcomm⟩ := fixV_comm_eq_UT he₀ hXc hfXc hXN (isElemAbelian2_iff.1 hXe)
  have hR : (rho11 AutPerm le_rfl).range.map (congrHom (rhoM24 g)) = img11 AutPerm :=
    (map_congrHom_self (⟨g, rfl⟩ : rhoM24 g ∈ (rho11 AutPerm le_rfl).range)).trans
      (range_rho11_eq_img11 AutPerm le_rfl)
  have hH : H.map (congrHom (twistEquiv e₀ rhoM24 g)) = img11 AutPerm :=
    (map_congrHom_trans e₀ (rhoM24 g) H).trans
      ((congrArg (fun K => K.map (congrHom (rhoM24 g))) he₀).trans hR)
  obtain ⟨hPS, -⟩ := lu_coc_std card_stab_UT_le
  have hP : perfectCore (img11 AutPerm ⊓ stabSub (fixV (X.map (congrHom (twistEquiv e₀ rhoM24 g))))) =
      img11 trQ :=
    (congrArg (fun U => perfectCore (img11 AutPerm ⊓ stabSub U)) hXU).trans hPS
  have e1 : s828BPrime (img11 AutPerm) (X.map (congrHom (twistEquiv e₀ rhoM24 g))) =
      commV (X.map (congrHom (twistEquiv e₀ rhoM24 g))) ⊔ commV (img11 trQ) ⊔ UT :=
    congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·) rfl (congrArg commV hP)) hXU
  have hcomm : commV (X.map (congrHom (twistEquiv e₀ rhoM24 g))) ≤ commV (img11 trQ) ⊔ UT :=
    hXcomm.trans (le_of_eq std4_commV_sup.symm)
  exact ⟨twistEquiv e₀ rhoM24 g, hH,
    e1.trans ((sup_assoc _ _ _).trans ((sup_eq_right.2 hcomm).trans std4_commV_sup)), hP, hXU⟩

theorem mb2_828_of_std
    (h1 : MB2Field 4 ↥(commutant (maskSub 9 mbL8_mb) U0
      ((P2 : Subgroup (MulAut W9)) : Set (MulAut W9))))
    (h2 : MB2Field 2 ↥(commutant (maskSub 10 mb2B9) UC
      ((imgC hbQ : Subgroup (MulAut W10)) : Set (MulAut W10))))
    (h3 : MB2Field 4 ↥(commutant (maskSub 11 mb3L10) US
      ((imgCd sxP0 : Subgroup (MulAut W11)) : Set (MulAut W11))))
    (h4 : Nonempty (↥(commutant (maskSub 11 mb4L9) UT
      ((img11 trQ : Subgroup (MulAut W11)) : Set (MulAut W11))) ≃+*
        Matrix (Fin 2) (Fin 2) (ZMod 2))) : MB2_828 := by
  intro V _ _ H X hXN hXe
  refine ⟨?_, ?_, ?_⟩
  · rintro (⟨h, hX, hfX⟩ | ⟨h, hX, hfX⟩)
    · obtain ⟨e, hH, hX', -⟩ := row1_transport_mb hXN hXe h hX hfX
      obtain ⟨K, hK, hKf, hKc, hi⟩ := h1
      have hP : perfectCore (img9 ⊓ stabSub (fixV QW9)) = P2 :=
        (congrArg (fun U => perfectCore (img9 ⊓ stabSub U)) fixV_QW9).trans perfectCore_stab_U0
      exact ⟨K, hK, hKf, hKc,
        mb2_iso_of_std e H X hH hX' s828BPrime_img9_QW9 fixV_QW9 hP hi⟩
    · obtain ⟨e, hH, hB, hP, hU⟩ := mb2_row3_data hXN hXe h hX hfX
      obtain ⟨K, hK, hKf, hKc, hi⟩ := h3
      exact ⟨K, hK, hKf, hKc, mb2_iso_of_std e H X hH rfl hB hU hP hi⟩
  · rintro ⟨h, hX, hfX⟩
    obtain ⟨e, hH, hB, hP, hU⟩ := mb2_row2_data hXN hXe h hX hfX
    obtain ⟨K, hK, hKf, hKc, hi⟩ := h2
    exact ⟨K, hK, hKf, hKc, mb2_iso_of_std e H X hH rfl hB hU hP hi⟩
  · rintro ⟨h, hX, hfX⟩
    obtain ⟨e, hH, hB, hP, hU⟩ := mb2_row4_data hXN hXe h hX hfX
    exact mb2_iso_of_std e H X hH rfl hB hU hP h4

end Rows

end CFSG.Quasithin.H13.Mat

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.H13.Mat

theorem mb2_828_proved :
    MB2_828 :=
  mb2_828_of_std mb2_std_row1 mb2_std_row2 mb2_std_row3 mb2_std_row4

end CFSG.Quasithin.H13
