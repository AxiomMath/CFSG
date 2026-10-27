module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartOne.KF.F122Engine
public import CFSG.RankThree.PartOne.S11c.Sec66TFamily

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartTwo.Census

theorem false_of_conj_fixed {T X Y : Type} [Group T] [Finite T] [Group X] [Group Y] [Finite Y]
    {p : ℕ}
    (hp : p.Prime) (e : T ≃* X) {α : MulAut T} (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T)
    (ψ β : MulAut X) (hψ : fixSub (ψ * MulAut.congr e α * ψ⁻¹) = fixSub β)
    (eY : ↥(fixSub β) ≃* Y) (hY : 2 ≤ localRank p Y) (hLRA : LocalRankAut p T α) : False := by
  let e12 : ↥(fixSub α) ≃* Y :=
    (((fixSubEquiv e α).trans (fixSubEquiv ψ (MulAut.congr e α))).trans
      (MulEquiv.subgroupCongr hψ)).trans eY
  have hN : 2 ≤ localRank p ↥(fixSub α) := by
    rw [localRank_eq_of_mulEquiv e12 hp]
    exact hY
  exact false_of_localRank_fixed hp hαp hαinn (fixSub α) (fun y hy => hy) hN hLRA

end CFSG.RankThree.PartOne
