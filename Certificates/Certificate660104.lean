module

public import Certificates.Data.Asc1113M22
meta import Certificates.Data.Asc1113M22

public section

namespace Certificates

open CFSG.M23 CFSG.Mathieu.Asc1113M22

set_option maxRecDepth 10000 in
theorem certificate660104_wordA : evalGroupWord C4 wordA = S2 0 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660104_wordB : evalGroupWord C4 wordB = S2 1 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660104_wordZ : evalGroupWord S2 wordZ = z := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660104_wordG1 : evalGroupWord S2 wordG1 = g1 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660104_wordG2 : evalGroupWord S2 wordG2 = g2 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660104_wordG3 : evalGroupWord S2 wordG3 = g3 := by decide +kernel

set_option maxRecDepth 10000 in
theorem certificate660104_wordG4 : evalGroupWord S2 wordG4 = g4 := by decide +kernel

theorem certificate660104 :
    CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.C4 CFSG.Mathieu.Asc1113M22.wordA =
        CFSG.Mathieu.Asc1113M22.S2 0 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.C4 CFSG.Mathieu.Asc1113M22.wordB =
        CFSG.Mathieu.Asc1113M22.S2 1 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S2 CFSG.Mathieu.Asc1113M22.wordZ =
        CFSG.Mathieu.Asc1113M22.z ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S2 CFSG.Mathieu.Asc1113M22.wordG1 =
        CFSG.Mathieu.Asc1113M22.g1 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S2 CFSG.Mathieu.Asc1113M22.wordG2 =
        CFSG.Mathieu.Asc1113M22.g2 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S2 CFSG.Mathieu.Asc1113M22.wordG3 =
        CFSG.Mathieu.Asc1113M22.g3 ∧
      CFSG.M23.evalGroupWord CFSG.Mathieu.Asc1113M22.S2 CFSG.Mathieu.Asc1113M22.wordG4 =
        CFSG.Mathieu.Asc1113M22.g4 :=
  ⟨certificate660104_wordA, certificate660104_wordB, certificate660104_wordZ,
    certificate660104_wordG1, certificate660104_wordG2, certificate660104_wordG3,
    certificate660104_wordG4⟩

end Certificates
