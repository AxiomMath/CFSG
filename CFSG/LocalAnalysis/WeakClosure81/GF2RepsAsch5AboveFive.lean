module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5AS511
public import CFSG.LocalAnalysis.WeakClosure81.PSpFourPrimeE1Generation
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5PSp4B
public import CFSG.CGT.PushingUpLit.Transport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt OInf)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (W4Lem4_10 W4Lem4_11)
open CFSG.Blueprint (LieModel)

theorem shapeInEAS_psp4_aboveFive
    (h : Asch4_12ASAboveFive) {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    ShapeInEAS 1 (fun X _ => LieModel X .PSp 2 p 1) :=
  shapeInEAS_of_ambient_fstar (isoInvPred_lieModel _ _ _ _) fun Q _ _ T hs hnab hT hFT hP =>
    h Q T p hp hp5 hs hnab hP hT hFT

section Asch511

theorem asch5_11AS_of_aboveFive
    (h54 : Asch5_4) (h412 : Asch4_12ASAboveFive)
    (hPS : Asch5_PSp4Three) : Asch5_11AS :=
  asch5_11AS_of_shapes h54
    (fun p hp hp5 => shapeInEAS_psp4_aboveFive h412 hp hp5) hPS

section

theorem asch5_11AS_of_remaining_inputs (h54 : Asch5_4) : Asch5_11AS :=
  asch5_11AS_of_aboveFive h54 asch4_12ASAboveFive_holds asch5_PSp4Three_holds

end

end Asch511

end CFSG.LocalAnalysis.WeakClosure81
