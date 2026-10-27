module

public import CFSG.Sporadic.Bridge.J2Native
public import CFSG.RankThree.PartTwo.Sec17.J2NotGL4Words
import CFSG.Certificates.Kernel.J2GL4Sound
import Certificates.Kernel.J2GL4.Checks

namespace CertificateChecks.C40520

open CFSG.Sporadic.Bridge.J2 CFSG.RankThree.PartTwo.Sec17.J2NotGL4 CFSG.KC.J2GL4 CFSG.KD.J2GL4

theorem pX7 : wordM wx7 = toM mX7 := wordM_of_lwordL ch40520_wx7
theorem pY7 : wordM wy7 = toM mY7 := wordM_of_lwordL ch40520_wy7
theorem pA5 : wordM wa5 = toM mA5 := wordM_of_lwordL ch40520_wa5
theorem pB5 : wordM wb5 = toM mB5 := wordM_of_lwordL ch40520_wb5
theorem pY5 : wordM wy5 = toM mY5 := wordM_of_lwordL ch40520_wy5

theorem b0 : baseL 0 = mX7 := rfl
theorem b1 : baseL 1 = mY7 := rfl
theorem b2 : baseL 2 = mA5 := rfl
theorem b3 : baseL 3 = mB5 := rfl
theorem b4 : baseL 4 = mY5 := rfl

local macro "j2s" : tactic => `(tactic| simp only [wordM_append, wordM_pw, wordM_nil, pX7, pY7,
  pA5, pB5, pY5, termM, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
  pow_one, mul_assoc, b0, b1, b2, b3, b4])

end CertificateChecks.C40520

