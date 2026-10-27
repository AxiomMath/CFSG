module

public import Certificates.Data.Asc1113M22
meta import Certificates.Data.Asc1113M22

public section

namespace Certificates

open CFSG.M23 CFSG.Mathieu.Asc1113M22

set_option maxRecDepth 10000 in
theorem certificate660106_wordUA : evalGroupWord UC4 wordUA = S3 0 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660106_wordUB : evalGroupWord UC4 wordUB = S3 1 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660106_wordUU : evalGroupWord UC4 wordUU = S3 2 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660106_wordUu : evalGroupWord S3 wordUu = u := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660106_wordUG1 : evalGroupWord S3 wordUG1 = ug1 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660106_wordUG2 : evalGroupWord S3 wordUG2 = ug2 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660106_wordUG3 : evalGroupWord S3 wordUG3 = ug3 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660106_wordUG4 : evalGroupWord S3 wordUG4 = ug4 := by decide +kernel

theorem certificate660106 :
    CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.UC4 CFSG.Mathieu.Asc1113M22.wordUA =
        CFSG.Mathieu.Asc1113M22.S3 0 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.UC4 CFSG.Mathieu.Asc1113M22.wordUB =
        CFSG.Mathieu.Asc1113M22.S3 1 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.UC4 CFSG.Mathieu.Asc1113M22.wordUU =
        CFSG.Mathieu.Asc1113M22.S3 2 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S3 CFSG.Mathieu.Asc1113M22.wordUu =
        CFSG.Mathieu.Asc1113M22.u ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S3 CFSG.Mathieu.Asc1113M22.wordUG1 =
        CFSG.Mathieu.Asc1113M22.ug1 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S3 CFSG.Mathieu.Asc1113M22.wordUG2 =
        CFSG.Mathieu.Asc1113M22.ug2 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S3 CFSG.Mathieu.Asc1113M22.wordUG3 =
        CFSG.Mathieu.Asc1113M22.ug3 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S3 CFSG.Mathieu.Asc1113M22.wordUG4 =
        CFSG.Mathieu.Asc1113M22.ug4 :=
  ⟨certificate660106_wordUA, certificate660106_wordUB, certificate660106_wordUU,
    certificate660106_wordUu, certificate660106_wordUG1, certificate660106_wordUG2,
    certificate660106_wordUG3, certificate660106_wordUG4⟩

end Certificates
