module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Small
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.ParNAll
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MinDeg
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.O4Plus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.O4PlusUnique
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallApply
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.NormalCase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.RankOneCase
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Main
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.Blueprint (LieModel)

private theorem isDirSumOver_autQuot_of_eq_bot {W : Type} [CommGroup W]
    {S : Set (Subgroup (MulAut W))} {N : Subgroup W} (hN : N = ⊥)
    (h : IsDirSumOver S (fun X => commV (autQuot X N))) :
    IsDirSumOver S (fun X => commV (autQuot X (⊥ : Subgroup W))) := by
  subst hN
  exact h

private theorem mParam_mul_rk_le_of_eq_bot {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)}
    {I N : Subgroup W} (hN : N = ⊥) (hι : 0 < rk ↥I)
    (h : (E3.mParam (autSub (autQuot Y N) (I.map (QuotientGroup.mk' N))) : ℚ) *
        ((rk ↥(commV (autQuot L N)) : ℚ) / (rk ↥(I.map (QuotientGroup.mk' N)) : ℚ)) ≤
      (E3.mParam Y : ℚ)) :
    E3.mParam (autSub Y I) * rk ↥(commV L) ≤ E3.mParam Y * rk ↥I := by
  subst hN
  rw [mParam_autSub_autQuot_bot, rk_commV_autQuot_bot, rk_map_mk_bot] at h
  have hιq : (0 : ℚ) < rk ↥I := by exact_mod_cast hι
  rw [← mul_div_assoc, div_le_iff₀ hιq] at h
  exact_mod_cast h

theorem w4Thm14_5_of
    (hSz : ∀ (X : Type) [Group X] (f : ℕ), IsSz X f → Nat.card X = CFSG.Open.ordSuzuki (2 ^ f))
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    (h128 : W4Lem12_8) (hSmall : K14_5Small) (hNPA : KNatParNAll) : W4Thm14_5 := by
  intro W _ _ hW Y L T P e n _ hO2 hirr hL hTY hT hfixT hncard hshape hPL hpar hinf hnorm hcomm
    hN hn hmin K hK W₀ hW₀ hma han H hH
  have hmY : E3.mParam Y ≤ n + 1 := hma.trans (Nat.add_le_add_right han 1)
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hdeg : n + 1 < PartTwo.dMinDeg ↥L := lt_dMinDeg_of_nParam_of hSz hq hPL hN hn
  have hLne : L ≠ ⊥ := B15P4.ne_bot_of_isComponentOf hL
  have hYne : Y ≠ ⊥ := fun h => hLne (le_bot_iff.mp (h ▸ hL.1))
  have hfixH : fixV (⨆ X ∈ conjSet L Y, X) = ⊥ := by
    have hle : (⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) ≤ ⨆ X ∈ conjSet L Y, X :=
      iSup₂_le fun t ht =>
        le_iSup₂_of_le (L.map (MulAut.conj t).toMonoidHom) ⟨t, hTY ht, rfl⟩ le_rfl
    rw [eq_bot_iff, ← hfixT]
    intro v hv x hx
    exact hv x (hle hx)
  rcases h128 W hW Y hO2 (isBasicModule_of_isIrrOn hYne hirr) L hL (⨆ X ∈ conjSet L Y, X) rfl with
    h1 | ⟨hsumQ, I, hI, hineqQ⟩ | ⟨R, e', hRY, hsumR, hLR, hnatR, -, -⟩
  ·
    omega
  ·
    have hsumQ' := isDirSumOver_autQuot_of_eq_bot hfixH hsumQ
    have hsum := isDirSumOver_commV_of_autQuot_bot hsumQ'
    have hIc : I ≤ commV L := by
      rw [commV_eq_commSub, ← hI.1]
      exact commSub_mono le_top le_rfl
    have hIfix : I ⊓ fixV L = ⊥ := by
      rw [eq_bot_iff, ← commV_inf_fixV_eq_bot_of_isDirSumOver hL hfixH hsumQ']
      exact inf_le_inf_right _ hIc
    have hι : 0 < rk ↥I := by
      rw [Nat.pos_iff_ne_zero, Ne, rk_eq_zero_iff hW]
      exact WeakClosure81.ne_bot_of_mem_irrSet hI
    have hineq : E3.mParam (autSub Y I) * rk ↥(commV L) ≤ E3.mParam Y * rk ↥I :=
      mParam_mul_rk_le_of_eq_bot hfixH hι hineqQ
    have hm1 : E3.mParam (autSub Y I) ≤ n + 1 := by
      have h1 : E3.mParam (autSub Y I) * rk ↥I ≤ E3.mParam Y * rk ↥I :=
        (Nat.mul_le_mul_left _ (rk_mono hIc)).trans hineq
      exact (Nat.le_of_mul_le_mul_right h1 hι).trans hmY
    have hnormI : ∀ y ∈ Y, y ∈ stabSub I → y ∈ normalizer (L : Set (MulAut W)) :=
      fun y hy hyI => mem_normalizer_of_mem_stabSub hsum hI hy hyI
    have hshape' : Shape14_5 ↥L e := by
      rcases hshape with h | ⟨-, h⟩
      · rcases h with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    have hsmall := small_of_mem_irrSet hSmall hG2 h3D4 h2F4 hW hL hshape' hPL hpar hinf hN hn hI
      hIfix hnormI hm1
    by_cases hLn : (L.subgroupOf Y).Normal
    ·
      have hHL : H = L := hH.trans ((iSup_map_conj_eq_self_iff hL.1).mpr hLn)
      rcases normal_case hSz hNPA hW hO2 hirr hL hTY hT hncard hLn hPL hpar hinf hnorm hcomm
          hN hn hmin hK hW₀ hma hmY hsum hfixH hI hIfix hineq hsmall with h | h
      · exact Or.inr (Or.inl (by rw [hHL]; exact h))
      · exact Or.inr (Or.inr (by rw [hHL]; exact h))
    ·
      have hrk : IsL2 ↥L e ∨ IsSz ↥L e ∨ IsU3 ↥L e ∨ IsSU3 ↥L e := by
        rcases hshape with h | ⟨h, -⟩
        · exact h
        · exact absurd h hLn
      have hHL : H ≠ L := fun h' =>
        hLn ((iSup_map_conj_eq_self_iff hL.1).mp (hH.symm.trans h'))
      exact Or.inl ⟨hHL, hsum, rankOne_case hSz hW hO2 hirr hL hTY hT hncard hrk hPL hinf
        hnorm hN hn hK hW₀ hma hmY hsum hfixH hI hIfix hineq hsmall⟩
  ·
    have hR1 := conjSet_eq_singleton_of_o4Plus hL hT hfixT hncard hRY hsumR hLR hnatR
    obtain ⟨-, -, hnat⟩ :=
      o4Plus_of_conjSet_eq hSz hO2 hL hT hPL hinf hnorm hN hH hRY hsumR hLR hnatR hR1
    exact Or.inr (Or.inl hnat)

theorem w4Thm14_5_of_w4Lem12_8
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    (h128 : W4Lem12_8) (hSmall : K14_5Small) (hNPA : KNatParNAll) : W4Thm14_5 :=
  w4Thm14_5_of (fun _ _ _ h => CFSG.LocalAnalysis.EvenBN.GMSK.card_eq_ordSuzuki_of_lieModel_twistedB2 h)
    hG2 h3D4 h2F4 h128 hSmall hNPA

theorem w4Thm14_5_of_k14_5Small
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X)
    (hSmall : K14_5Small) (hNPA : KNatParNAll) : W4Thm14_5 :=
  w4Thm14_5_of_w4Lem12_8 hG2 h3D4 h2F4 CFSG.LocalAnalysis.WeakClosure81.w4Lem12_8_holds hSmall hNPA

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
