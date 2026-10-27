module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCStepsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCRed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.WeakClosure81

theorem tcReduction_of (hO : OrbitStmt) (hK : KillStmt) : TCReduction := by
  have hR := tcBarOfHyps_holds
  intro hC G _ _ V T N L hyp hTN hNM hN hL hψ hφ hstar
  obtain ⟨X, _, _, ψ, hs, hk, Lb, B, _, _, π, Es, hbar⟩ :=
    hR hC G V T N L hyp hTN hNM hN hL hψ hφ
  exact TC914.tcAbstract_of hO hK G V T N hyp hTN hNM hstar X ψ hs hk Lb B π Es hbar

theorem tcReduction_of_lemmas (hO : OrbitStmt) (hK : KillStmt) : TCReduction :=
  tcReduction_of hO hK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
