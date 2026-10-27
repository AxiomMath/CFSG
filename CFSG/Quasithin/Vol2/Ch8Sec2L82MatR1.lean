module

public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatGen
public import CFSG.Quasithin.Vol2.Ch8Sec2L828MBRow1

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.L3W9 CFSG.Quasithin.H.L34Z CFSG.Quasithin.H.LU
  CFSG.Quasithin.E3 CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H13 CFSG.Quasithin.H.Coc

@[expose] def mb1R1L2 : List ℕ := [323, 163, 1, 354, 211, 16, 3, 443]

theorem mb1R1_L2_gen : ∀ l ∈ mb1R1L2, (∃ c ∈ [colsX2, colsY2], ∃ b ∈ mbL8_mb,
    l = actM c b ^^^ b) ∨ l ∈ combos U0Basis := by decide +kernel

theorem mb1R1_cover : ∀ l ∈ mbL8_mb, l ∈ combos mb1R1L2 := by decide +kernel

theorem actsBy_rho9_x2 : ActsBy (rho9 x2G) colsX2 :=
  actsBy_of_lt (by decide) fun m hm => rho9_toW_cols x2G cols_x2.1 hm

theorem actsBy_rho9_y2 : ActsBy (rho9 y2G) colsY2 :=
  actsBy_of_lt (by decide) fun m hm => rho9_toW_cols y2G cols_x2.2.1 hm

theorem mb1_std_row1 :
    s828CommSub P2 (maskSub 9 mbL8_mb) ⊔ U0 = maskSub 9 mbL8_mb := by
  refine le_antisymm (sup_le ((s828CommSub_le_commV _ _).trans commP_le_mb) U0_le_mb) ?_
  have h := maskSub_le_commSub_sup_of_cover (n := 9) (S := {rho9 x2G, rho9 y2G})
    (L := mbL8_mb) (L2 := mb1R1L2) (Ub := U0Basis) ?_ mb1R1_cover
  · exact h
  · intro l hl
    rcases mb1R1_L2_gen l hl with ⟨c, hc, b, hb, hl'⟩ | hU
    · left
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨rho9 x2G, Set.mem_insert _ _, _, actsBy_rho9_x2, b, hb, hl'⟩
      · exact ⟨rho9 y2G, Set.mem_insert_of_mem _ rfl, _, actsBy_rho9_y2, b, hb, hl'⟩
    · exact Or.inr hU

theorem s828BPrime_img9_QW9 :
    s828BPrime img9 QW9 = maskSub 9 mbL8_mb := by
  have hP : perfectCore (img9 ⊓ stabSub (fixV QW9)) = P2 :=
    (congrArg (fun U => perfectCore (img9 ⊓ stabSub U)) fixV_QW9).trans perfectCore_stab_U0
  have e1 : s828BPrime img9 QW9 = commV QW9 ⊔ commV P2 ⊔ U0 :=
    congrArg₂ (· ⊔ ·) (congrArg₂ (· ⊔ ·) rfl (congrArg commV hP)) fixV_QW9
  exact e1.trans BStd_eq_mb

theorem mb1_std_row1' :
    s828CommSub (perfectCore (img9 ⊓ stabSub (fixV QW9))) (s828BPrime img9 QW9) ⊔ fixV QW9 =
      s828BPrime img9 QW9 := by
  have hP : perfectCore (img9 ⊓ stabSub (fixV QW9)) = P2 :=
    (congrArg (fun U => perfectCore (img9 ⊓ stabSub U)) fixV_QW9).trans perfectCore_stab_U0
  have h1 : s828CommSub (perfectCore (img9 ⊓ stabSub (fixV QW9))) (s828BPrime img9 QW9) ⊔
      fixV QW9 = s828CommSub P2 (maskSub 9 mbL8_mb) ⊔ U0 :=
    congrArg₂ (· ⊔ ·) (congrArg₂ s828CommSub hP s828BPrime_img9_QW9) fixV_QW9
  exact h1.trans (mb1_std_row1.trans s828BPrime_img9_QW9.symm)

theorem mb1_row1 {V : Type} [CommGroup V] [Finite V]
    {H X : Subgroup (MulAut V)} (hXN : X ≤ Subgroup.normalizer (H : Set (MulAut V)))
    (hXe : IsElemAbelian2 X) (h : BinaryNineTensor H ⊤ ⊥ 1) (hX : rk ↥X = 4)
    (hfX : rk ↥(fixV X) = 4) :
    s828CommSub (perfectCore (H ⊓ stabSub (fixV X))) (s828BPrime H X) ⊔ fixV X =
      s828BPrime H X := by
  obtain ⟨e, hH, hX', -⟩ := row1_transport_mb hXN hXe h hX hfX
  exact mb1_eq_of_map' e H X img9 QW9 hH hX' mb1_std_row1'

end CFSG.Quasithin.H13.Mat
