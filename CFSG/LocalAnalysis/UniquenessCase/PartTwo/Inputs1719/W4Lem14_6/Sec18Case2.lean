module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.O4Plus
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Structure
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem case2_of_fix_of_lt_dMinDeg {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L X : Subgroup (MulAut W)}
    (hO2 : O2Trivial Y) (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hfix : fixV X = ⊥)
    (hd : E3.mParam Y < dMinDeg ↥L) (hnL2 : ∀ e : ℕ, ¬ IsL2 ↥L e) :
    IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
        (fun X' => commV (autQuot X' (⊥ : Subgroup W))) ∧
      ∃ I ∈ irrSet L,
        (E3.mParam (autSub Y I) : ℚ) * ((rk ↥(commV L) : ℚ) / (rk ↥I : ℚ)) ≤ E3.mParam Y := by
  have hHX : (⨆ X' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X') = X := by
    rw [iSup_conjSet_eq_biSup_conj, hX]
  rcases w4Lem12_8_holds W hW Y hO2 hB L hL X hHX.symm with
    h1 | ⟨hsum, I, hI, hIm⟩ | ⟨R, e, -, -, hLR, hnat, -, -⟩
  · exfalso
    omega
  · have key : ∀ N : Subgroup W, N = ⊥ →
        IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
          (fun X' => commV (autQuot X' N)) →
        (E3.mParam (autSub (autQuot Y N) (I.map (QuotientGroup.mk' N))) : ℚ) *
            ((rk ↥(commV (autQuot L N)) : ℚ) /
              (rk ↥(I.map (QuotientGroup.mk' N)) : ℚ)) ≤ E3.mParam Y →
        IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
            (fun X' => commV (autQuot X' (⊥ : Subgroup W))) ∧
          (E3.mParam (autSub Y I) : ℚ) * ((rk ↥(commV L) : ℚ) / (rk ↥I : ℚ)) ≤
            E3.mParam Y := by
      rintro N rfl hs hi
      refine ⟨hs, ?_⟩
      rwa [Thm14_5.mParam_autSub_autQuot_bot, Thm14_5.rk_commV_autQuot_bot,
        Thm14_5.rk_map_mk_bot] at hi
    obtain ⟨hs, hi⟩ := key (fixV X) hfix hsum hIm
    exact ⟨hs, I, hI, hi⟩
  · exfalso
    exact hnL2 e (Thm14_5.isL2_of_isSubnormal_isNaturalO4Plus hL.2.2 hLR hnat)

theorem commSub_commSub_eq_bot_of_dirSum {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hsum : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
      (fun X' => commV (autQuot X' (⊥ : Subgroup W))))
    {g : MulAut W} (hg : g ∈ Y) (hgN : g ∉ normIn Y L) :
    commSub (commSub (⊤ : Subgroup W) L) (L.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  set B : Subgroup (MulAut W) := L.map (MulAut.conj g).toMonoidHom with hB
  have hBmem : B ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y := ⟨g, hg, hB⟩
  have hLmem : L ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y :=
    ⟨1, Y.one_mem, by ext x; simp [MulAut.conj_apply]⟩
  have hBL : B ≠ L := by
    intro h
    have hnorm : g ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hB.symm.trans h)
    exact hgN (by simpa [normIn] using ⟨hg, hnorm⟩)
  have hsum' : IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y) commV :=
    Thm14_5.isDirSumOver_commV_of_autQuot_bot hsum
  have hdisj : Disjoint (commV L) (commV B) :=
    hsum'.1.pairwiseDisjoint (i := ⟨L, hLmem⟩) (j := ⟨B, hBmem⟩)
      (fun h => hBL (congrArg Subtype.val h).symm)
  have hA : commSub (commSub (⊤ : Subgroup W) L) B ≤ commV L := by
    rw [commV_eq_commSub]
    refine commSub_le_of_invariant ?_
    intro x hx w hw
    have hw' : w ∈ commV L := by rwa [commV_eq_commSub]
    rw [fix_commV_of_mem_conjSet_of_ne hL hsum hBmem hLmem hBL x hx w hw']
    exact hw
  have hA' : commSub (commSub (⊤ : Subgroup W) L) B ≤ commV B := by
    calc commSub (commSub (⊤ : Subgroup W) L) B ≤ commSub (⊤ : Subgroup W) B :=
          commSub_mono le_top le_rfl
      _ = commV B := (commV_eq_commSub B).symm
  rw [eq_bot_iff]
  intro u hu
  exact hdisj.le_bot ⟨hA hu, hA' hu⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
