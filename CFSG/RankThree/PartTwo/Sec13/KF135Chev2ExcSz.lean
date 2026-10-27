module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Vacuous
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.RankThree.PartTwo.Sec13.KF135Proof CFSG.LieType.SeitzGeneration


theorem false_of_kF135Hyp_suzuki {S : Type} [Group S] [Finite S] {p : ℕ}
    {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)} {m : ℕ}
    {hv : (TauCeti.LieTypeIndex.suzuki m).Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) (h : KF135Hyp S p P x u V) :
    False := by
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.seven_le
    omega
  have hr : RankLE1 p S :=
    RankLE1.of_mulEquiv e.symm
      (CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.rankLE1_cat_suzuki hv hp hp2)
  have hout := (CFSG.RankThree.PartOne.OutStructure.outPNice_Suzuki hp
    (CFSG.StandardType.ChevTwo.suzukiModel_of_valid m hv e)).toChain
  exact false_of_rankLE1 h hout hr

theorem kF135At_fam7Sz : KF135At Fam7Sz := by
  intro S _ _ p P x u V hS h
  obtain ⟨m, hm, ⟨e⟩⟩ := hS
  exact (false_of_kF135Hyp_suzuki e h).elim

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc
