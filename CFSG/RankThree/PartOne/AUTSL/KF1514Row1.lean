module

public import CFSG.RankThree.PartOne.AUTSL.L4Aut
public import CFSG.RankThree.PartOne.KSP6.Transport
public import CFSG.RankThree.PartOne.S15K.ProjSLBridge

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG CFSG.Assembly.RankThreeEven CFSG.LocalAnalysis.ComponentInitial

theorem kf1514PAut_one : KF1514PAut 1 := by
  intro p f hp h5 hf hpf
  have hf0 : f ≠ 0 := by omega
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  have e : ↥(projSL 4 (GaloisField 2 f)) ≃* Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 f) :=
    (CFSG.RankThree.PartOne.S15K.projSLEquivProjectiveSL 4 (GaloisField 2 f)).trans
      (LinearCover.projectiveSLFourEquivSL (GaloisField 2 f))
  have : Finite ↥(projSL 4 (GaloisField 2 f)) := Finite.of_equiv _ e.symm.toEquiv
  exact KSP6.kf1514PAutGen_of_mulEquiv e hp
    (L4.kf1514PAutGen_SL4 hp h5 hq (by rwa [hq]))

end CFSG.RankThree.PartOne.AUTSL
