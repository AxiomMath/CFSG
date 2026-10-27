module

public import CFSG.Monster.B.CTIB.WordsInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits
import CFSG.Certificates.Kernel.BabyMonster.CTIBWordsSound
import all Init.Data.List.SplitOn.Basic
public import CFSG.Monster.B.CTIB.CosetBase

public section

open CFSG.Monster.B.CTIB

namespace CertificateChecks.Batch3110

open CFSG.Monster.B.CTIB

private theorem parseWords_centWordStr_0 :
    Native.parseWords Native.centWordStr = Native.centWordsL := by
  str_lits Native.centWordStr
  exact (Native.parseWords_ofList _).trans (eq_of_beq (by quickRfl))

private theorem parseWords_centWordStr_neg :
    (!(Native.parseWords Native.centWordStr == Native.centWordsL.set 44 [1])) = true := by
  str_lits Native.centWordStr
  rw [Native.parseWords_ofList]
  quickRfl

end CertificateChecks.Batch3110

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.CTIB in
theorem certificate3110 : Native.parseWords Native.centWordStr = Native.centWordsL ∧ centLettersOK = true :=
  ⟨CertificateChecks.Batch3110.parseWords_centWordStr_0, by quickRfl⟩

end Certificates
