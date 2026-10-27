module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42LinkCheck
public import CFSG.Open.LocalVocabulary
import CFSG.Certificates.Kernel.HTD42Glue
import Certificates.Certificate9415
import Certificates.Kernel.D4Plane.Checks
import Certificates.Kernel.HTD42.Checks
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434D42Check

public section

namespace Certificates

open CFSG.KD.D4Plane

open CFSG.RankThree.PartTwo.Sec4.Item434D42 (lineGroup) in
theorem certificate264001 : Subgroup.center CFSG.RankThree.PartTwo.Sec4.Item434D42.lineGroup = ⊥ → Nat.card (MulAut CFSG.RankThree.PartTwo.Sec4.Item434D42.lineGroup) = 3 * 211341312 →
    ∀ α : MulAut CFSG.RankThree.PartTwo.Sec4.Item434D42.lineGroup, (∀ g : CFSG.RankThree.PartTwo.Sec4.Item434D42.lineGroup, α ≠ MulAut.conj g) → α ^ 3 = 1 →
      ∃ F : Subgroup CFSG.RankThree.PartTwo.Sec4.Item434D42.lineGroup, CFSG.Open.IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ ∀ x ∈ F, α x = x :=
  CFSG.KC.HTD42G.outerFix_of (ls := ls) (es := es)
    (fun i hi => beq_iff_eq.1 (List.all_eq_true.1 lettersOK i (List.mem_range.2 hi))) enumOK
    CFSG.KD.HTD42Q.normA CFSG.KD.HTD42Q.normB CFSG.KD.HTD42Q.cubeX CFSG.KD.HTD42Q.frobX
    CFSG.KD.HTD42Q.planesOK CFSG.KD.HTD42Q.witA CFSG.KD.HTD42Q.witB

end Certificates
