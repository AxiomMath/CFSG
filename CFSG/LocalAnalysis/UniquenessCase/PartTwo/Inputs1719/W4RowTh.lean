module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowAutInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowDihedral
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Th

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.Family CFSG.Blueprint
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

theorem w4Thm11_1RowM_Th_holds :
    W4Thm11_1RowM .Th := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e⟩ := hs
  have hYL : Y = L := W4Row.eq_of_fstar_eq_of_autInner hLY hLn hF hq e th_autInner
  show 9 ≤ E3.mParam Y
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have h19 : 19 ∣ Nat.card (NativeSporadic.Carrier .Th) := by
    have h := orderOf_dvd_natCard
      (CFSG.Sporadic.Th.a * (thDihC * CFSG.Sporadic.Th.a * thDihC⁻¹))
    rw [orderOf_thDih, ← Nat.card_congr CFSG.Sporadic.Th.thEquivJ.toEquiv] at h
    exact h
  exact W4Row.le_mParam_of_dihedral hW hO2 (fun t ht _ => hYL.le ht) e (p := 19) (by norm_num)
    h19 (by rw [CFSG.QuasithinUnique.Setup.X1.orderOf_two_zmod_19]) th_dihedral

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
