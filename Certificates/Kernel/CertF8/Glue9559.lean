module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28SUCheck
public import Certificates.Data.Kernel.CertF8.SU9559
public import Certificates.Data.Kernel.CertF8.Pack
import CFSG.Certificates.Kernel.CertF8.PackSound
import Certificates.Kernel.CertF8.Check9559

public section

namespace Certificates.Kernel.CertF8

open CFSG.KC.CertF8 CFSG.KC.G28 CFSG.AGLEmbedding.KFactProofs.G28
  CFSG.AGLEmbedding.KFactProofs.G28.SU CFSG.RankThree.PartTwo.Sec4.Item434G28
open scoped Matrix

theorem valid_suP : Valid suP := by decide +kernel

theorem valid_suPi : Valid suPi := by decide +kernel

theorem valid_rCode : Valid rCode := by decide +kernel

theorem valid_w5Code : Valid w5Code := by decide +kernel

theorem valid_aCodes : ∀ k : Fin 7, Valid aCodes[k.val]! := by decide +kernel

theorem decode_rCode : decode rCode = rbM := by decide +kernel

theorem trace_w5Code : Matrix.trace (decode w5Code) = CFSG.Quasithin.GF8.ofNat' 6 := by
  decide +kernel

theorem aCodes_ok : ∀ k : Fin 7, (decode aCodes[k.val]!)ᵀ * jbM * decode aCodes[k.val]! = jbM ∧
    detBlk (decode aCodes[k.val]!) = 1 := by
  decide +kernel

theorem codeP_tzc : codeP tzc = powS6 (wordS6 tUW) 3 := by
  rw [tzc, tU, codeP_powCode6 (valid_wordCode _), codeP_wordCode6]

theorem valid_tzc : Valid tzc := valid_powCode (valid_wordCode _) 3

theorem mul3 {X Y Z : Array ℕ} (hX : Valid X) (hY : Valid Y) (hZ : Valid Z) {C : Array ℕ}
    (hC : Valid C) (h : mulS6 (mulS6 (codeP X) (codeP Y)) (codeP Z) = codeP C) :
    decode X * decode Y * decode Z = decode C := by
  have e : codeP (mulCode (mulCode X Y) Z) = codeP C := by
    rw [codeP_mulCode6 (valid_mulCode hX hY) hZ, codeP_mulCode6 hX hY, h]
  rw [← decode_mulCode hX hY, ← decode_mulCode (valid_mulCode hX hY) hZ]
  exact congrArg decode (codeP_inj (valid_mulCode (valid_mulCode hX hY) hZ) hC e)

theorem mul2 {X Y : Array ℕ} (hX : Valid X) (hY : Valid Y)
    (h : mulS6 (codeP X) (codeP Y) = idP) : decode X * decode Y = 1 := by
  have e : codeP (mulCode X Y) = codeP idCode := by
    rw [codeP_mulCode6 hX hY, h, codeP_idCode]
  rw [← decode_mulCode hX hY, ← decode_idCode]
  exact congrArg decode (codeP_inj (valid_mulCode hX hY) valid_idCode e)

theorem aMat_eq (k : Fin 7) : aMat k = decode aCodes[k.val]! := by
  have h := ch9559A k
  rw [← codeP_wordCode6] at h
  exact mul3 valid_suPi (valid_wordCode _) valid_suP (valid_aCodes k) h

theorem suOK9559 : suOK := by
  refine ⟨mul2 valid_suP valid_suPi ch9559P.1, mul2 valid_suPi valid_suP ch9559P.2, ?_,
    fun k => ?_, ?_⟩
  · have h := ch9559R
    rw [← codeP_tzc] at h
    rw [mP, mPi, mul3 valid_suPi valid_tzc valid_suP valid_rCode h,
      decode_rCode]
  · rw [aMat_eq k]
    exact aCodes_ok k
  · have h := ch9559W
    rw [← codeP_wordCode6] at h
    rw [codeP_inj (valid_wordCode _) valid_w5Code h]
    exact trace_w5Code

end Certificates.Kernel.CertF8

end
