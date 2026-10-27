module

public import Certificates.Kernel.Co2Eleven.C16960K
public import Certificates.Kernel.Co2Eleven.Glue
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits
import CFSG.Certificates.Kernel.Spor.TabWords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Eleven

open CFSG.KC.Co2Eleven CFSG.KC.SlpM CertificateChecks.KernelSporSch.Co2M
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative

theorem words7_txt : co2SevenWordsStr = String.ofList (wordsC wcK7) := by
  str_lits co2SevenWordsStr
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

theorem words7_eq : co2SevenData.words = wsK7.toArray := by
  have e : ∀ s, parseIntLists s =
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative.parseIntLists s :=
    fun _ => rfl
  change parseIntLists co2SevenWordsStr = _
  rw [words7_txt, e, parseIntLists_wordsC (by decide +kernel)]
  rfl

theorem slp7_ok : CFSG.Sporadic.Fi23.Native.slpOK co2SevenData.words = true := by
  have h : (List.range wsK7.length).all (fun j => (wsK7.getD j []).all fun z =>
      z != 0 && (decide (z.natAbs ≤ 2) || decide (z.natAbs < j + 3))) = true := by
    decide +kernel
  rw [words7_eq]
  unfold CFSG.Sporadic.Fi23.Native.slpOK
  rw [CFSG.KS.TW.allIn_iff]
  intro j hj
  rw [List.size_toArray] at hj
  have := List.all_eq_true.1 h j (List.mem_range.2 hj)
  rw [getElem!_pos _ j (by simpa using hj), List.getElem_toArray]
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this

theorem seven_ok : co2SevenOK co2SevenData 7 56 = true := by
  have hc : co2SevenData.chain.toList = chainW7 := rfl
  have hd : co2SevenData.id.toList = idW7 := rfl
  have hi : co2SevenData.is = 3 := rfl
  have hh : co2SevenData.ih = 4 := rfl
  refine sevenK_sound (A := AP 0) (B := AP 1) (WV := WV7) (WVI := WVI7) (R := R7) (szs := SZ7)
    (gen_eq (by norm_num)) (gen_eq (by norm_num)) slp7_ok rfl ?_ ?_
  · rw [words7_eq, List.toList_toArray, hc, hi, hh]
    unfold elevenK
    rw [letters7_k, levels7_k, count7_k, misc7_k]
    rfl
  · rw [words7_eq, List.toList_toArray, hd, hi, hh]
    exact cent7_k

end CertificateChecks.KernelCo2Eleven

end
