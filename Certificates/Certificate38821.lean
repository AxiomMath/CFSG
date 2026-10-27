module

public import Certificates.Data.SmithD6Uw
public import Mathlib.Logic.Relation
import Certificates.Kernel.SmithD6UwB.Glue
import Certificates.Kernel.SmithD6Pinned.Holds

public section

namespace Certificates

open CertificateChecks.SmithD6Pinned CertificateChecks.SmithD6UwB

theorem certificate38821 : CFSG.SmithD6.uw7ChkE0 () = true ∧
    CFSG.SmithD6.uw7ChkLevi () = true ∧
    CFSG.SmithD6.uw7ChkBCls () = true ∧
    (∀ v < 75735, CFSG.SmithD6.uw7InB (CFSG.SmithD6.uw7E0 ()) v = true → Relation.ReflTransGen
      (fun a b => ∃ g < 30, CFSG.SmithD6.uw7InB (CFSG.SmithD6.uw7E0 ()) a = true ∧
        CFSG.SmithD6.uw7InB (CFSG.SmithD6.uw7E0 ()) b = true ∧
        CFSG.SmithD6.uw7BCls (CFSG.SmithD6.uw7E0 ()) a =
          CFSG.SmithD6.uw7BCls (CFSG.SmithD6.uw7E0 ()) b ∧
        CFSG.SmithD6.planeImg (CFSG.SmithD6.uw7LLines ())[g]! a = b)
      ((CFSG.SmithD6.uw7BReps ())[CFSG.SmithD6.uw7BCls (CFSG.SmithD6.uw7E0 ()) v - 1]!) v) ∧
    (∀ v < 75735, CFSG.SmithD6.uw7InB (CFSG.SmithD6.uw7E0 ()) v = true →
      CFSG.SmithD6.uw7BCls (CFSG.SmithD6.uw7E0 ()) v = 1 →
      ∃ k < 365211, (CFSG.SmithD6.linePair k).1 &&& 63 = 0 ∧
        (CFSG.SmithD6.linePair k).2 &&& 63 = 0 ∧
        CFSG.SmithD6.planeImgM (CFSG.SmithD6.tvCols k) (CFSG.SmithD6.uw7E0 ()) = v) :=
  have hW := pinnedModel.wtArr_toList
  have hpb := pinnedModel.pbArr_get
  have hpp := pinnedModel.ppArr_get
  have hL := pinnedModel.lineIdx_of_memB
  ⟨uw7ChkE0_of_pinned hW hpb hpp, uw7ChkLevi_of_pinned hW hpb hpp hL,
    uw7ChkBCls_of_pinned hW hpb hpp, uw7B_of_pinned hW hpb hpp hL,
    uw7Wit_of_pinned hW hpb hpp hL⟩

end Certificates
