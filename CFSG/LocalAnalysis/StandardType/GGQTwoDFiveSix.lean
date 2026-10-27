module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSeven
public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6Raw
import CFSG.LocalAnalysis.StandardType.GGQTwoDGNSix
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr5Main
import CFSG.LocalAnalysis.StandardType.GGQTwoDNbr6TwE6
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMFiveSix
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelFive
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorHolds
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthCell

public section

namespace CFSG.StandardType.QTwo

theorem ggCoxeterMatrixD_five_not_far (i k j l : Fin 5) (hik : ggCoxeterMatrixD 5 i k = 3)
    (hjl : ggCoxeterMatrixD 5 j l = 3) (hij : ggCoxeterMatrixD 5 i j = 2)
    (hil : ggCoxeterMatrixD 5 i l = 2) (hkj : ggCoxeterMatrixD 5 k j = 2)
    (hkl : ggCoxeterMatrixD 5 k l = 2) : False := by
  have h : ∀ q : Fin 5 × Fin 5 × Fin 5 × Fin 5, ggCoxeterMatrixD 5 q.1 q.2.1 = 3 →
      ggCoxeterMatrixD 5 q.2.2.1 q.2.2.2 = 3 → ggCoxeterMatrixD 5 q.1 q.2.2.1 = 2 →
      ggCoxeterMatrixD 5 q.1 q.2.2.2 = 2 → ggCoxeterMatrixD 5 q.2.1 q.2.2.1 = 2 →
      ggCoxeterMatrixD 5 q.2.1 q.2.2.2 = 2 → False := by
    decide +kernel
  exact h (i, k, j, l) hik hjl hij hil hkj hkl

private theorem le_of_fiveSix {k : ℕ} (hk : k ≤ 5) (m : ℕ) (hm : m = 5 ∨ m = 6) : k ≤ m := by
  rcases hm with rfl | rfl <;> omega

section Producer


theorem GGQTwoFarInputOn.or {R R' : ℕ → Prop} {cell : QTwoCell} (h : GGQTwoFarInputOn R cell)
    (h' : GGQTwoFarInputOn R' cell) : GGQTwoFarInputOn (fun m => R m ∨ R' m) cell := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm
  rcases hm with hm | hm
  · exact h G p B Bs x L D J 𝒦 ι M e hcfg m e' hm
  · exact h' G p B Bs x L D J 𝒦 ι M e hcfg m e' hm

theorem GGQTwoCellInputOn.or {R R' : ℕ → Prop} {cell : QTwoCell} (h : GGQTwoCellInputOn R cell)
    (h' : GGQTwoCellInputOn R' cell) : GGQTwoCellInputOn (fun m => R m ∨ R' m) cell := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm
  rcases hm with hm | hm
  · exact h G p B Bs x L D J 𝒦 ι M e hcfg m e' hm
  · exact h' G p B Bs x L D J 𝒦 ι M e hcfg m e' hm

theorem ggQTwoFarInputOn_five (cell : QTwoCell) : GGQTwoFarInputOn (fun m => m = 5) cell := by
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hc i k j l hik hjl hij hil hkj hkl
  subst hm
  exact (ggCoxeterMatrixD_five_not_far i k j l hik hjl hij hil hkj hkl).elim

theorem ggSecFivePhanDQTwoFiveSix_of_inputs (hRk1 : GGSecFiveRk1PhanInput)
    (hL1 : GGQTwoL1InputOn fun m => m = 5 ∨ m = 6)
    (hGen : GGQTwoGenInputOn fun m => m = 5 ∨ m = 6)
    (hOrth : GGQTwoCellInputOn (fun m => m = 5 ∨ m = 6) qtwoOrthL)
    (hUnit : GGQTwoCellInputOn (fun m => m = 5 ∨ m = 6) qtwoOrthL.compl)
    (hFarOrth : GGQTwoFarInputOn (fun m => m = 6) qtwoOrthL)
    (hFarUnit : GGQTwoFarInputOn (fun m => m = 6) qtwoOrthL.compl) :
    GGSecFivePhanDQTwoFiveSix :=
  GGSecFivePhanDQTwoAt.of_cells
    (ggSecFivePhanDQTwoCell_of_inputs (le_of_fiveSix le_rfl) hRk1 hL1 hGen hOrth
      ((ggQTwoFarInputOn_five _).or hFarOrth))
    (ggSecFivePhanDQTwoCell_of_inputs (le_of_fiveSix le_rfl) hRk1 hL1 hGen hUnit
      ((ggQTwoFarInputOn_five _).or hFarUnit))

end Producer

section Leaves


theorem ggSecFivePhanDQTwoFiveSix_of_leaves
    (hRk1 : GGSecFiveRk1PhanInput) (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hZS : ZS.UseInput) (hTCJ : GGTCJKnown) (hLB : GGLBalanceInput) (hPJ : GGStdSubPrimeInput)
    (hRk : GGTwE6ThreeNbrRankInput)
    (hUnit : GGQTwoCellInputOn (fun m => m = 5 ∨ m = 6) qtwoOrthL.compl)
    (hFarOrth : GGQTwoFarInputOn (fun m => m = 6) qtwoOrthL)
    (hFarUnit : GGQTwoFarInputOn (fun m => m = 6) qtwoOrthL.compl) :
    GGSecFivePhanDQTwoFiveSix := by
  have hNonc : GGLNoncyclicInput := ggLNoncyclicInput_holds
  have hOrth : GGQTwoCellInputOn (fun m => m = 5 ∨ m = 6) qtwoOrthL :=
    ggQTwoCellInputOn_orth_fiveSix hTBF hWI
  have hRM6 : GGQTwoRMInputOn fun m => m = 6 := ggQTwoRMInputOn_six hTBF hWI hZS
  have hSel : GGQTwoDSelModuleInputOn fun m => m = 6 :=
    ggQTwoDSelModuleInputOn_of_selectedModule (R := fun m => m = 6) (fun m hm => by omega) hTBF hWI
  have hOJ : GGQTwoDOrthJInput := ggQTwoDOrthJInput_holds
  have hTw : GGQTwoDSixTwE6InputOn fun m => m = 6 := ggQTwoDSixTwE6InputOn_of_nbrRank hRk
  have hGN : GGQTwoGNInputOn fun m => m = 5 ∨ m = 6 :=
    (ggQTwoGNInputOn_five hTBF hWI (ggQTwoRMInputOn_five hTBF hWI) hTCJ hLB hPJ hRk).or
      (ggQTwoGNInputOn_six hTBF hWI hRM6 hTCJ hLB hPJ hTw)
  exact ggSecFivePhanDQTwoFiveSix_of_inputs hRk1
    (ggQTwoL1InputOn_fiveSix hNonc hTBF hWI hRM6 hTCJ hLB hPJ hSel hOJ hTw)
    (ggQTwoGenInput_of_absorb (le_of_fiveSix (by decide)) hNonc
      (ggQTwoRMInputOn_five_six hTBF hWI hZS) hGN
      ((ggQTwoSelLInputOn_five hTBF hWI).or
        (ggQTwoSelLInputOn_six hNonc hTBF hWI hRM6 hTCJ hLB hPJ hSel hOJ hTw))
      (ggQTwoEdgeLeInput_of_cells (le_of_fiveSix le_rfl) hOrth hUnit))
    hOrth hUnit hFarOrth hFarUnit

end Leaves

end CFSG.StandardType.QTwo

end
