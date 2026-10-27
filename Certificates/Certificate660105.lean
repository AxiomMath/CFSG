module

public import Certificates.Data.Asc1113M22
meta import Certificates.Data.Asc1113M22

public section

namespace Certificates

open CFSG.M23 CFSG.Mathieu.Asc1113M22

set_option maxRecDepth 10000 in
theorem certificate660105_wordTA : evalGroupWord TC4 wordTA = S3 0 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660105_wordTB : evalGroupWord TC4 wordTB = S3 1 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660105_wordTU : evalGroupWord TC4 wordTU = S3 2 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660105_wordTt : evalGroupWord S3 wordTt = t := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660105_wordTG1 : evalGroupWord S3 wordTG1 = tg1 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660105_wordTG2 : evalGroupWord S3 wordTG2 = tg2 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660105_wordTG3 : evalGroupWord S3 wordTG3 = tg3 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660105_wordTG4 : evalGroupWord S3 wordTG4 = tg4 := by decide +kernel

theorem certificate660105 :
    CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.TC4 CFSG.Mathieu.Asc1113M22.wordTA =
        CFSG.Mathieu.Asc1113M22.S3 0 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.TC4 CFSG.Mathieu.Asc1113M22.wordTB =
        CFSG.Mathieu.Asc1113M22.S3 1 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.TC4 CFSG.Mathieu.Asc1113M22.wordTU =
        CFSG.Mathieu.Asc1113M22.S3 2 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S3 CFSG.Mathieu.Asc1113M22.wordTt =
        CFSG.Mathieu.Asc1113M22.t ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S3 CFSG.Mathieu.Asc1113M22.wordTG1 =
        CFSG.Mathieu.Asc1113M22.tg1 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S3 CFSG.Mathieu.Asc1113M22.wordTG2 =
        CFSG.Mathieu.Asc1113M22.tg2 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S3 CFSG.Mathieu.Asc1113M22.wordTG3 =
        CFSG.Mathieu.Asc1113M22.tg3 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S3 CFSG.Mathieu.Asc1113M22.wordTG4 =
        CFSG.Mathieu.Asc1113M22.tg4 :=
  ⟨certificate660105_wordTA, certificate660105_wordTB, certificate660105_wordTU,
    certificate660105_wordTt, certificate660105_wordTG1, certificate660105_wordTG2,
    certificate660105_wordTG3, certificate660105_wordTG4⟩

end Certificates
