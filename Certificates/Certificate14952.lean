module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKD4Comm
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKElem
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatTriality

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.K1 CFSG.QuasithinUnique.K1.ExceptionalCat
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

namespace D4Exam

private theorem cert14952_weyl_x6_x5 :
    List.ofFn (reflect TwistTag.D4.tag ⟨2, by decide⟩ (trialityRoot 5)) =
      List.ofFn (trialityRoot 4) := by
  decide +kernel

private theorem cert14952_weyl_x5_x2 :
    List.ofFn (reflect TwistTag.D4.tag ⟨0, by decide⟩ (reflect TwistTag.D4.tag ⟨1, by decide⟩
      (reflect TwistTag.D4.tag ⟨3, by decide⟩ (trialityRoot 4)))) =
      List.ofFn (trialityRoot 1) := by
  decide +kernel

private theorem cert14952_trialityRoot_one : List.ofFn (trialityRoot 1) = List.ofFn rC := by
  decide +kernel

private theorem cert14952_trialityRoot_four : List.ofFn (trialityRoot 4) = List.ofFn rP := by
  decide +kernel

private theorem cert14952_trialityRoot_five : List.ofFn (trialityRoot 5) = List.ofFn rH := by
  decide +kernel

private theorem cert14952_x1_h0 : List.ofFn (trialityRoot 0) = List.ofFn rE0 := by
  decide +kernel

private theorem cert14952_x1_h1 : List.ofFn (permLattice TwistTag.D4.perm rE0) = List.ofFn rE1 := by
  decide +kernel

private theorem cert14952_x1_h2 :
    List.ofFn (permLattice (TwistTag.D4.perm ^ 2) rE0) = List.ofFn rE3 := by
  decide +kernel

private theorem cert14952_x3_h0 : List.ofFn (trialityRoot 2) = List.ofFn rM0 := by
  decide +kernel

private theorem cert14952_x3_h1 : List.ofFn (permLattice TwistTag.D4.perm rM0) = List.ofFn rM1 := by
  decide +kernel

private theorem cert14952_x3_h2 :
    List.ofFn (permLattice (TwistTag.D4.perm ^ 2) rM0) = List.ofFn rM3 := by
  decide +kernel

private theorem cert14952_x4_h0 : List.ofFn (trialityRoot 3) = List.ofFn rN13 := by
  decide +kernel

private theorem cert14952_x4_h1 :
    List.ofFn (permLattice TwistTag.D4.perm rN13) = List.ofFn rN03 := by
  decide +kernel

private theorem cert14952_x4_h2 :
    List.ofFn (permLattice (TwistTag.D4.perm ^ 2) rN13) = List.ofFn rN01 := by
  decide +kernel

end D4Exam

end CFSG.QuasithinUnique.Lin2

namespace Certificates

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique.Lin2.D4Exam in
theorem certificate14952 :
    (List.ofFn (reflect TwistTag.D4.tag ⟨2, by decide⟩ (trialityRoot 5)) =
      List.ofFn (trialityRoot 4)) ∧
    (List.ofFn (reflect TwistTag.D4.tag ⟨0, by decide⟩ (reflect TwistTag.D4.tag ⟨1, by decide⟩
      (reflect TwistTag.D4.tag ⟨3, by decide⟩ (trialityRoot 4)))) =
      List.ofFn (trialityRoot 1)) ∧
    (List.ofFn (trialityRoot 1) = List.ofFn rC) ∧
    (List.ofFn (trialityRoot 4) = List.ofFn rP) ∧
    (List.ofFn (trialityRoot 5) = List.ofFn rH) ∧
    (List.ofFn (trialityRoot 0) = List.ofFn rE0) ∧
    (List.ofFn (permLattice TwistTag.D4.perm rE0) = List.ofFn rE1) ∧
    (List.ofFn (permLattice (TwistTag.D4.perm ^ 2) rE0) = List.ofFn rE3) ∧
    (List.ofFn (trialityRoot 2) = List.ofFn rM0) ∧
    (List.ofFn (permLattice TwistTag.D4.perm rM0) = List.ofFn rM1) ∧
    (List.ofFn (permLattice (TwistTag.D4.perm ^ 2) rM0) = List.ofFn rM3) ∧
    (List.ofFn (trialityRoot 3) = List.ofFn rN13) ∧
    (List.ofFn (permLattice TwistTag.D4.perm rN13) = List.ofFn rN03) ∧
    (List.ofFn (permLattice (TwistTag.D4.perm ^ 2) rN13) = List.ofFn rN01) := by
  exact ⟨CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_weyl_x6_x5,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_weyl_x5_x2,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_trialityRoot_one,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_trialityRoot_four,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_trialityRoot_five,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_x1_h0,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_x1_h1,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_x1_h2,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_x3_h0,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_x3_h1,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_x3_h2,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_x4_h0,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_x4_h1,
    CFSG.QuasithinUnique.Lin2.D4Exam.cert14952_x4_h2⟩

end Certificates
