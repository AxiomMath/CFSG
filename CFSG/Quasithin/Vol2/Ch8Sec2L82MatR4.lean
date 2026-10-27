module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatP
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR4L
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR4S
public import CFSG.Quasithin.Background.HLURows

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.LU CFSG.Quasithin.H.Coc24
  CFSG.Quasithin.E3 CFSG.Quasithin.H13

section Final

variable
  {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)}

private theorem row4_data
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

theorem mb0_row4 (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCocode24 H ⊤ ⊥) (hX : rk ↥X = 6) (hfX : rk ↥(fixV X) = 3) :
    mQuot ⊤ (s828BPrime H X) = 2 := by
  obtain ⟨e, hH, hB, -, -⟩ := row4_data hXN hXe h hX hfX
  exact (mb0_of_map' e H X _ _ hH rfl).trans ((congrArg (mQuot ⊤) hB).trans std4_mQuot)

theorem mb1_row4 (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCocode24 H ⊤ ⊥) (hX : rk ↥X = 6) (hfX : rk ↥(fixV X) = 3) :
    s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X =
      s828BPrime H X := by
  obtain ⟨e, hH, hB, hP, hU⟩ := row4_data hXN hXe h hX hfX
  refine mb1_eq_of_map' e H X _ _ hH rfl ?_
  have h1 : s828CommSub (perfectCore (img11 AutPerm ⊓ stabSub (fixV (X.map (congrHom e)))))
        (s828BPrime (img11 AutPerm) (X.map (congrHom e))) ⊔ fixV (X.map (congrHom e)) =
      s828CommSub (img11 trQ) (maskSub 11 mb4L9) ⊔ UT :=
    congrArg₂ (· ⊔ ·) (congrArg₂ s828CommSub hP hB) hU
  exact h1.trans (std4_MB1.trans hB.symm)

theorem mb3_row4 (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCocode24 H ⊤ ⊥) (hX : rk ↥X = 6) (hfX : rk ↥(fixV X) = 3) :
    ∀ x ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))), ∀ b ∈ s828BPrime H X,
      x b * b⁻¹ ∈ fixV X := by
  obtain ⟨e, hH, hB, hP, hU⟩ := row4_data hXN hXe h hX hfX
  refine mb3_of_map' e H X _ _ hH rfl ?_
  intro x hx b hb
  have hx' : x ∈ pCoreOf 2 (img11 trQ) :=
    Eq.mp (congrArg (fun K => x ∈ pCoreOf 2 K) hP) hx
  obtain ⟨-, htop, hsimple, hnc, -⟩ := lu_coc_std (card_stab_UT_le)
  have hstab : img11 trQ ≤ stabSub UT := img11_trQ_le.trans inf_le_right
  have := hsimple
  have hxC : x ∈ centSub UT := pCoreOf_le_centSub hstab hnc hx'
  have hxP : x ∈ img11 trQ := Subgroup.map_subtype_le _ hx'
  have hb' : b ∈ maskSub 11 mb4L9 := Eq.mp (congrArg (fun K => b ∈ K) hB) hb
  have := std4_trivK card_stab_UT_le x ⟨hxP, hxC⟩ b hb'
  exact Eq.mpr (congrArg (fun K => x b * b⁻¹ ∈ K) hU) this

end Final

end CFSG.Quasithin.H13.Mat
