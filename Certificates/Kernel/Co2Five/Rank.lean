module

public import Certificates.Kernel.Co2Five.RankK
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Misc.PairCountSound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Five

open CFSG.KC.Enum CFSG.KS.Raw CertificateChecks.KernelSporSch.Co2M
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native CFSG.RankThree.Native

theorem arr_eq {r : Nat} (hr : r < 2) : co2FiveArr r = unpack 2300 12 (Co2FiveTxt.F r) := by
  rw [co2FiveArr, Co2FiveTxt.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable3_sound Co2FiveTxt.all r hr

theorem lineDiff_eq {r i : Nat} (hr : r < 2) (hi : i < 2300) (hlt : lineK r i < 2300) :
    co2LineDiff r i = lineDiffK r i := by
  have e : co2FiveLineArr r = unpack 2300 12 (Co2FiveTxt.F r) := by
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · exact arr_eq (r := 0) (by norm_num)
    · exact arr_eq (r := 1) (by norm_num)
  unfold co2LineDiff lineDiffK
  have hk : pg 12 (CFSG.KS.mask 12) (Co2FiveTxt.F r) i = lineK r i := rfl
  rw [e, CFSG.KC.Misc.PairCount.unpack_get hi, hk, V_get hlt, V_get hi]

theorem rankOf_eq {r : Nat} (hr : r < 2) (hlt : ∀ i < 2300, lineK r i < 2300)
    (idx dual : List Nat) : co2RankCheckOf r idx dual = rankOfK r idx dual := by
  unfold co2RankCheckOf rankOfK
  by_cases h : (idx.all (· < 2300)) = true
  · have hm : ∀ l, idx.getD l 0 < 2300 := by
      intro l
      rw [List.getD_eq_getElem?_getD]
      cases e : idx[l]? with
      | none => simp
      | some x =>
        simp only [Option.getD_some]
        exact of_decide_eq_true (List.all_eq_true.1 h x (List.mem_of_getElem? e))
    rw [h]
    simp only [Bool.true_and]
    have h' : ∀ l, co2LineDiff r (idx.getD l 0) = lineDiffK r (idx.getD l 0) :=
      fun l => lineDiff_eq hr (hm l) (hlt _ (hm l))
    simp only [h']
  · rw [Bool.not_eq_true] at h
    rw [h]
    rfl

theorem rank_ok : co2RankCheck () = true := by
  have h := rank_k
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp, h0⟩, h1⟩ := h
  have hl : ∀ r < 2, ∀ i < 2300, lineK r i < 2300 := by
    intro r hr i hi
    have := CFSG.KS.allN_spec hp i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · exact this.1
    · exact this.2
  unfold co2RankCheck
  rw [rankOf_eq (by norm_num) (hl 0 (by norm_num)), rankOf_eq (by norm_num) (hl 1 (by norm_num)),
    h0, h1]
  rfl

end CertificateChecks.KernelCo2Five

end
