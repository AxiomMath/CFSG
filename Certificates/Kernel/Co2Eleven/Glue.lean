module

public import Certificates.Kernel.Co2Eleven.C17707K
public import CFSG.Certificates.Kernel.Co2ElevenSound
public import CFSG.Certificates.Kernel.Spor.SlpTextSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits
import CFSG.Certificates.Kernel.Spor.TabWords

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Eleven

open CFSG.KC.Co2Eleven CFSG.KC.SlpM CertificateChecks.KernelSporSch.Co2M
open CFSG.HardMathSupport.Dickson.BMRows.Co2ElevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co2SevenNative

theorem words_txt : co2ElevenWordsStr = String.ofList (wordsC wcK) := by
  str_lits co2ElevenWordsStr
  exact congrArg String.ofList (of_decide_eq_true (by quickRfl))

theorem words_eq : co2ElevenData.words = wsK.toArray := by
  have e : ∀ s, parseIntLists s =
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative.parseIntLists s :=
    fun _ => rfl
  change parseIntLists co2ElevenWordsStr = _
  rw [words_txt, e, parseIntLists_wordsC (by decide +kernel)]
  rfl

theorem gen_eq {k : Nat} (hk : k < 2) :
    co2T k = (CFSG.KS.Raw.unpack 2300 12 (AP k)).map UInt32.ofNat := by
  unfold co2T
  rw [← aArrs_get hk]
  rfl

theorem slp_ok : CFSG.Sporadic.Fi23.Native.slpOK co2ElevenData.words = true := by
  have h : (List.range wsK.length).all (fun j => (wsK.getD j []).all fun z =>
      z != 0 && (decide (z.natAbs ≤ 2) || decide (z.natAbs < j + 3))) = true := by
    decide +kernel
  rw [words_eq]
  unfold CFSG.Sporadic.Fi23.Native.slpOK
  rw [CFSG.KS.TW.allIn_iff]
  intro j hj
  rw [List.size_toArray] at hj
  have := List.all_eq_true.1 h j (List.mem_range.2 hj)
  rw [getElem!_pos _ j (by simpa using hj), List.getElem_toArray]
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this

theorem eleven_ok : co2ElevenCheck () = true := by
  refine elevenK_sound (A := AP 0) (B := AP 1) (WV := WV) (WVI := WVI) (R := R) (szs := SZ)
    (gen_eq (by norm_num)) (gen_eq (by norm_num)) slp_ok ?_
  rw [words_eq, List.toList_toArray]
  have hc : co2ElevenData.chain.toList = chainW := rfl
  have hi : co2ElevenData.is = 33 := rfl
  have hh : co2ElevenData.ih = 34 := rfl
  rw [hc, hi, hh]
  unfold elevenK
  rw [letters_k, levels_k, count_k, misc_k]
  rfl

end CertificateChecks.KernelCo2Eleven

end
