module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR2L
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatR2S
public import CFSG.Quasithin.Background.HLURows

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Code22 CFSG.Quasithin.H.LU
  CFSG.Quasithin.E3
  CFSG.Quasithin.H13

section Final

variable
  {V : Type} [CommGroup V] [Finite V] {H X : Subgroup (MulAut V)}

private theorem row2_data
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

theorem mb0_row2 (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCode22 H ⊤ ⊥) (hX : rk ↥X = 5) (hfX : rkIdx (fixV X) = 6) :
    mQuot ⊤ (s828BPrime H X) = 1 := by
  obtain ⟨e, hH, hB, -, -⟩ := row2_data hXN hXe h hX hfX
  exact (mb0_of_map' e H X _ _ hH rfl).trans ((congrArg (mQuot ⊤) hB).trans std2_mQuot)

theorem mb1_row2 (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCode22 H ⊤ ⊥) (hX : rk ↥X = 5) (hfX : rkIdx (fixV X) = 6) :
    (s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X).relIndex
      (s828BPrime H X) = 2 := by
  obtain ⟨e, hH, hB, hP, hU⟩ := row2_data hXN hXe h hX hfX
  refine mb1_relIndex_of_map' e H X _ _ hH rfl ?_
  have h1 : (s828CommSub (perfectCore (imgC mog22 ⊓ stabSub (fixV (X.map (congrHom e)))))
        (s828BPrime (imgC mog22) (X.map (congrHom e))) ⊔ fixV (X.map (congrHom e))).relIndex
        (s828BPrime (imgC mog22) (X.map (congrHom e))) =
      (s828CommSub (imgC hbQ) (maskSub 10 mb2B9) ⊔ UC).relIndex (maskSub 10 mb2B9) :=
    congrArg₂ Subgroup.relIndex (congrArg₂ (· ⊔ ·) (congrArg₂ s828CommSub hP hB) hU) hB
  exact h1.trans std2_MB1

theorem mb3_row2 (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V))) (hXe : IsElemAbelian2 X)
    (h : MathieuCode22 H ⊤ ⊥) (hX : rk ↥X = 5) (hfX : rkIdx (fixV X) = 6) :
    ∀ x ∈ pCoreOf 2 (perfectCore (H ⊓ stabSub (fixV X))), ∀ b ∈ s828BPrime H X,
      x b * b⁻¹ ∈ fixV X := by
  obtain ⟨e, hH, hB, hP, hU⟩ := row2_data hXN hXe h hX hfX
  refine mb3_of_map' e H X _ _ hH rfl ?_
  intro x hx b hb
  have hx' : x ∈ pCoreOf 2 (imgC hbQ) := Eq.mp (congrArg (fun K => x ∈ pCoreOf 2 K) hP) hx
  have hxQ : x ∈ imgC Q16P := pCoreOf_imgC_hbQ_le hx'
  have hb' : b ∈ maskSub 10 mb2B9 := Eq.mp (congrArg (fun K => b ∈ K) hB) hb
  have := std2_trivK x hxQ b hb'
  exact Eq.mpr (congrArg (fun K => x b * b⁻¹ ∈ K) hU) this

end Final

end CFSG.Quasithin.H13.Mat
