module

public import CFSG.RankThree.PartTwo.Sec13.KF135Fam4G2
public import CFSG.RankThree.PartTwo.Sec13.KF135Fam4Sp4
public import CFSG.RankThree.PartTwo.Sec13.KF135Fam4L4
public import CFSG.RankThree.PartTwo.Sec13.KF135Fam4U4
public import CFSG.RankThree.PartTwo.Sec13.KF135Fam4U4Gate

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof

theorem gateU4_holds : FamOdd.GateU4 :=
  fun _ _ _ _ hr hp7 hpr A hA hAc => FamOdd.false_of_elemAbelian_psu4 hr hp7 hpr A hA hAc

section Fam4


theorem kF135At_fam4_of_gate (hgate : FamOdd.GateU4) : KF135At Fam4 := by
  intro S _ _ p P x u V hF h
  obtain ⟨r, hr, hr3, hG2 | hSp | hSL | hSU⟩ := hF
  · obtain ⟨q, hqp, hqe, hiso⟩ := hG2
    exact (FamOdd.g2_hyp_false (by rw [hqp]; exact hr3) hqe hiso h).elim
  · obtain ⟨φ⟩ := hSp
    exact (FamOdd.psp4_hyp_false hr3 φ h).elim
  · obtain ⟨φ⟩ := hSL
    exact (FamOdd.psl4_hyp_false hr3 φ h).elim
  · obtain ⟨φ⟩ := hSU
    exact (FamOdd.psu4_hyp_false_of_gate hgate hr3 φ h).elim

theorem kF135At_fam4 : KF135At Fam4 :=
  kF135At_fam4_of_gate gateU4_holds

end Fam4

end CFSG.RankThree.PartTwo.Sec13.KF135Proof
