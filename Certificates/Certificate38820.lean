module

public import Certificates.Data.SmithD6Uw
public import Mathlib.Logic.Relation
import Certificates.Kernel.SmithD6Uw.Dist
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks.SmithD6Pinned CertificateChecks.SmithD6Uw

theorem certificate38820 : CFSG.SmithD6.uw7ChkGens () = true ∧
    CFSG.SmithD6.uw7ChkCls () = true ∧
    (∀ v < 75735, Relation.ReflTransGen
      (fun a b => ∃ g < 45, CFSG.SmithD6.uw7Cls a = CFSG.SmithD6.uw7Cls b ∧
        CFSG.SmithD6.planeImg (CFSG.SmithD6.uw7Gens ())[g]! a = b)
      ((CFSG.SmithD6.uw7Reps ())[CFSG.SmithD6.uw7Cls v]!) v) ∧
    CFSG.SmithD6.uw7ChkDist () = true :=
  ⟨uw7ChkGens_of_pinned pinnedModel.wtArr_toList pinnedModel.lineIdx_of_memB,
    uw7ChkCls_of_pinned pinnedModel.wtArr_toList,
    uw7Orb_of_pinned pinnedModel.wtArr_toList pinnedModel.lineIdx_of_memB,
    uw7ChkDist_of_pinned pinnedModel.pbArr_get pinnedModel.ppArr_get pinnedModel.wtArr_toList⟩

end Certificates
