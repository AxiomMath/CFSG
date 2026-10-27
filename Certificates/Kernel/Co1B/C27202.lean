module

public import Certificates.Kernel.Co1B.Chk27202
public import Certificates.Kernel.Co1B.C27207
public import CFSG.Certificates.Kernel.Co1BPairSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Pair27202

open CFSG.KC.Co1BPair CFSG.KC.Co1BSpin CFSG.KC.Co1B CFSG.KC.Co1F2 CFSG.KC.F2W CFSG.KLie.CT
  CFSG.EvenSporadicStandard.Co1Pair CFSG.Sporadic.Co1Schreier.Native

theorem cpNums_eq : cpNums = (numsOf PT.chars).toArray := by
  have h : cpNums = CFSG.EvenSporadicStandard.G24Model.parseNums cpText := rfl
  have hg : (PT.chars.splitOn ' ').all CertificateChecks.EvenSporG24.goodK = true := kGood
  rw [h, PT.eq]
  exact CertificateChecks.EvenSporG24.parseNums_ofList _ hg

theorem lens : T.H.length = 6 ∧ T.SW.length = 5 ∧ T.TW0.length = 1365 ∧ T.TW1.length = 1024 ∧
    T.TW2.length = 180 ∧ T.D0.length = 9555 ∧ T.D1.length = 5120 ∧ T.D2.length = 540 ∧
    T.TW0.head? = some [] ∧ T.TW1.head? = some [] ∧ T.TW2.head? = some [] := by
  have h := kLen
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem hL : numsOf PT.chars = T.H ++ encW T.SW ++ encW T.TW0 ++ encW T.TW1 ++ encW T.TW2 ++
    T.D0 ++ T.D1 ++ T.D2 ++ T.R := leqK_sound kNums

theorem ss_eq : cpSsRead = (T.SW.toArray, (T.H ++ encW T.SW).length) := by
  have h : cpSsRead = cpReadWords cpNums 5 6 := rfl
  have e : numsOf PT.chars = T.H ++ (encW T.SW ++ (encW T.TW0 ++ encW T.TW1 ++ encW T.TW2 ++
      T.D0 ++ T.D1 ++ T.D2 ++ T.R)) := by
    rw [hL]
    simp only [List.append_assoc]
  rw [h, cpNums_eq, e, ← lens.2.1, ← lens.1, readWords_enc, List.length_append]

theorem tw0_eq : cpTwRead0 = (T.TW0.toArray, (T.H ++ encW T.SW ++ encW T.TW0).length) := by
  have h : cpTwRead0 = cpReadWords cpNums (cpN 0) cpSsRead.2 := rfl
  have e : numsOf PT.chars = (T.H ++ encW T.SW) ++ (encW T.TW0 ++ (encW T.TW1 ++ encW T.TW2 ++
      T.D0 ++ T.D1 ++ T.D2 ++ T.R)) := by
    rw [hL]
    simp only [List.append_assoc]
  have hn : cpN 0 = T.TW0.length := by rw [lens.2.2.1]; rfl
  rw [h, ss_eq, cpNums_eq, e, hn, readWords_enc]
  simp only [List.length_append]

theorem tw1_eq : cpTwRead1 = (T.TW1.toArray, (T.H ++ encW T.SW ++ encW T.TW0 ++ encW T.TW1).length) := by
  have h : cpTwRead1 = cpReadWords cpNums (cpN 1) cpTwRead0.2 := rfl
  have e : numsOf PT.chars = (T.H ++ encW T.SW ++ encW T.TW0) ++ (encW T.TW1 ++ (encW T.TW2 ++
      T.D0 ++ T.D1 ++ T.D2 ++ T.R)) := by
    rw [hL]
    simp only [List.append_assoc]
  have hn : cpN 1 = T.TW1.length := by rw [lens.2.2.2.1]; rfl
  rw [h, tw0_eq, cpNums_eq, e, hn, readWords_enc]
  simp only [List.length_append]

theorem tw2_eq : cpTwRead2 =
    (T.TW2.toArray, (T.H ++ encW T.SW ++ encW T.TW0 ++ encW T.TW1 ++ encW T.TW2).length) := by
  have h : cpTwRead2 = cpReadWords cpNums (cpN 2) cpTwRead1.2 := rfl
  have e : numsOf PT.chars = (T.H ++ encW T.SW ++ encW T.TW0 ++ encW T.TW1) ++ (encW T.TW2 ++
      (T.D0 ++ T.D1 ++ T.D2 ++ T.R)) := by
    rw [hL]
    simp only [List.append_assoc]
  have hn : cpN 2 = T.TW2.length := by rw [lens.2.2.2.2.1]; rfl
  rw [h, tw1_eq, cpNums_eq, e, hn, readWords_enc]
  simp only [List.length_append]

theorem cptw0 : cpTw 0 = T.TW0.toArray := by
  have h : cpTw 0 = cpTwRead0.1 := rfl
  rw [h, tw0_eq]

theorem cptw1 : cpTw 1 = T.TW1.toArray := by
  have h : cpTw 1 = cpTwRead1.1 := rfl
  rw [h, tw1_eq]

theorem cptw2 : cpTw 2 = T.TW2.toArray := by
  have h : cpTw 2 = cpTwRead2.1 := rfl
  rw [h, tw2_eq]

theorem dec0_eq : cpDec 0 = T.D0.toArray := by
  have h : cpDec 0 = cpNums.extract cpTwRead2.2 (cpTwRead2.2 + cpN 0 * (7 - cpF 0)) := rfl
  have e : numsOf PT.chars = (T.H ++ encW T.SW ++ encW T.TW0 ++ encW T.TW1 ++ encW T.TW2) ++
      (T.D0 ++ (T.D1 ++ T.D2 ++ T.R)) := by
    rw [hL]
    simp only [List.append_assoc]
  have hn : cpN 0 * (7 - cpF 0) = T.D0.length := by rw [lens.2.2.2.2.2.1]; rfl
  rw [h, tw2_eq, cpNums_eq, e, hn, extract_mid]

theorem dec1_eq : cpDec 1 = T.D1.toArray := by
  have h : cpDec 1 = cpNums.extract (cpTwRead2.2 + cpN 0 * (7 - cpF 0))
      (cpTwRead2.2 + cpN 0 * (7 - cpF 0) + cpN 1 * (7 - cpF 1)) := rfl
  have e : numsOf PT.chars = (T.H ++ encW T.SW ++ encW T.TW0 ++ encW T.TW1 ++ encW T.TW2 ++ T.D0) ++
      (T.D1 ++ (T.D2 ++ T.R)) := by
    rw [hL]
    simp only [List.append_assoc]
  have hn0 : cpN 0 * (7 - cpF 0) = T.D0.length := by rw [lens.2.2.2.2.2.1]; rfl
  have hn : cpN 1 * (7 - cpF 1) = T.D1.length := by rw [lens.2.2.2.2.2.2.1]; rfl
  rw [h, tw2_eq, cpNums_eq, e, hn0, hn, ← List.length_append, extract_mid]

theorem dec2_eq : cpDec 2 = T.D2.toArray := by
  have h : cpDec 2 = cpNums.extract (cpTwRead2.2 + cpN 0 * (7 - cpF 0) + cpN 1 * (7 - cpF 1))
      (cpTwRead2.2 + cpN 0 * (7 - cpF 0) + cpN 1 * (7 - cpF 1) + cpN 2 * (7 - cpF 2)) := rfl
  have e : numsOf PT.chars =
      (T.H ++ encW T.SW ++ encW T.TW0 ++ encW T.TW1 ++ encW T.TW2 ++ T.D0 ++ T.D1) ++
      (T.D2 ++ T.R) := by
    rw [hL]
    simp only [List.append_assoc]
  have hn0 : cpN 0 * (7 - cpF 0) = T.D0.length := by rw [lens.2.2.2.2.2.1]; rfl
  have hn1 : cpN 1 * (7 - cpF 1) = T.D1.length := by rw [lens.2.2.2.2.2.2.1]; rfl
  have hn : cpN 2 * (7 - cpF 2) = T.D2.length := by rw [lens.2.2.2.2.2.2.2.1]; rfl
  rw [h, tw2_eq, cpNums_eq, e, hn0, hn1, hn, ← List.length_append, ← List.length_append,
    extract_mid]

theorem arr_get! (a : Array (Array Nat)) (j : Nat) : a[j]! = a.toList.getD j #[] := by
  cases a
  simp [List.getD_eq_getElem?_getD]
  rfl

theorem getL_G7 {j : Nat} (hj : j < 7) : getL 0 G7 j = P.M j := by
  rw [getL_eq, G7, List.getElem?_map, List.getElem?_range hj]
  rfl

theorem x_eq : cpX = unpackR 24 (P.M 0) := by
  rw [Cent27207.cpX_eq]
  exact (beq_of_eqK kX).symm

theorem y_eq : cpY = unpackR 24 (P.M 1) := by
  rw [Cent27207.cpY_eq]
  exact (beq_of_eqK kY).symm

theorem xy_get {l : Nat} (hl : l < 2) :
    (#[cpX, cpY] : Array (Array Nat))[l]! = unpackR 24 (getL 0 [P.M 0, P.M 1] l) := by
  interval_cases l
  · simp [x_eq, getL_eq]
  · simp [y_eq, getL_eq]

theorem ss_get {j : Nat} (hj : j < 7) : cpSs[j]! = unpackR 24 (getL 0 G7 j) := by
  have ht : cpSs.toList = [cpX, cpY] ++ T.SW.map (cpWord #[cpX, cpY]) := by
    simp [cpSs, ss_eq]
  rw [arr_get!, ht, getL_G7 hj]
  rcases Nat.lt_or_ge j 2 with h | h
  · interval_cases j
    · rw [x_eq]
      rfl
    · rw [y_eq]
      rfl
  · obtain ⟨t, rfl⟩ : ∃ t, j = t + 2 := ⟨j - 2, by omega⟩
    have htl : t < T.SW.length := by rw [lens.2.1]; omega
    have hw := wordsK_sound kS t htl
    rw [List.getD_append_right _ _ _ _ (by simp), List.length_cons, List.length_cons,
      List.length_nil, Nat.add_sub_cancel, List.getD_eq_getElem _ _ (by simpa using htl),
      List.getElem_map, cpWord_eq (Gk := [P.M 0, P.M 1]) (fun l hl => xy_get (by simpa using hl))
        (fun l hl => by simpa using (hw.1 l hl).2), ← hw.2]
    congr 2
    omega

theorem tms_get {i k : Nat} (hi : i < 3) :
    cpTMget i k = ((cpTw i).map (cpWord cpSs))[k]! := by
  rw [cpTMget, if_pos hi]
  interval_cases i <;> rfl

theorem tm_get' {i : Nat} (hi : i < 3) {TW : List (List Nat)} (htw : cpTw i = TW.toArray)
    (hk : wordsK P.M G7 (cpF i) 7 (offK i) TW 0 = true) {k : Nat} (hkl : k < TW.length) :
    cpTMget i k = unpackR 24 (tmK P.M i k) := by
  have hw := wordsK_sound hk k hkl
  have hlt : Nat.blt i 3 = true := Eq.mpr Nat.blt_eq hi
  have ht : tmK P.M i k = P.M (offK i + k) := by
    change Bool.rec (motive := fun _ => Nat) oneK (P.M (Nat.add (offK i) k)) (Nat.blt i 3) = _
    rw [hlt]
    rfl
  rw [tms_get hi, htw, ht, arr_get!]
  rw [Array.toList_map, List.toList_toArray, List.getD_eq_getElem _ _ (by simpa using hkl),
    List.getElem_map, cpWord_eq (Gk := G7) (fun l hl => ss_get (by simpa [G7] using hl))
      (fun l hl => by simpa [G7] using (hw.1 l hl).2), ← hw.2, Nat.zero_add]

theorem tm_get {i k : Nat} (h : i < 3 → k < cpN i) : cpTMget i k = unpackR 24 (tmK P.M i k) := by
  rcases Nat.lt_or_ge i 3 with hi | hi
  · have hk := h hi
    interval_cases i
    · exact tm_get' (i := 0) (by decide) cptw0 kT0 (by rw [lens.2.2.1]; exact hk)
    · exact tm_get' (i := 1) (by decide) cptw1 kT1 (by rw [lens.2.2.2.1]; exact hk)
    · exact tm_get' (i := 2) (by decide) cptw2 kT2 (by rw [lens.2.2.2.2.1]; exact hk)
  · have hlt : Nat.blt i 3 = false := by
      rw [Bool.eq_false_iff]
      intro e
      exact absurd (Eq.mp Nat.blt_eq e) (by omega)
    rw [cpTMget, if_neg (by omega), one_eq]
    change _ = unpackR 24 (Bool.rec (motive := fun _ => Nat) oneK (P.M (Nat.add (offK i) k)) (Nat.blt i 3))
    rw [hlt]

theorem cpN_pos (j : Nat) : 0 < cpN j := by
  unfold cpN
  rcases j with _ | _ | _ | _ | _ | j <;> simp

theorem level_ok {i : Nat} (hi : i < 3) {TW : List (List Nat)} {D : List Nat}
    (htw : cpTw i = TW.toArray) (hdec : cpDec i = D.toArray) (hlen : TW.length = cpN i)
    (hhead : TW.head? = some []) (hk : wordsK P.M G7 (cpF i) 7 (offK i) TW 0 = true)
    (hD : D.length = cpN i * (7 - cpF i)) (hlev : levK P.M i D 0 = true) (hF : cpF i < 7) :
    cpLevelOK i = true := by
  unfold cpLevelOK
  rw [htw, hdec]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  have hg : 0 < 7 - cpF i := by omega
  refine ⟨⟨⟨⟨by simp [hlen], ?_⟩, ?_⟩, by simp [hD]⟩, ?_⟩
  · cases TW with
    | nil => simp at hhead
    | cons w rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      rfl
  · rw [Array.all_eq_true]
    intro s hs
    have hs' : s < TW.length := by simpa using hs
    have hw := (wordsK_sound hk s hs').1
    simp only [List.getElem_toArray, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact fun l hl => hw l hl
  · intro k hk jj hjj
    have hs : k * (7 - cpF i) + jj < D.length := by
      rw [hD]
      calc k * (7 - cpF i) + jj < k * (7 - cpF i) + (7 - cpF i) := Nat.add_lt_add_left hjj _
        _ = (k + 1) * (7 - cpF i) := by rw [Nat.succ_mul]
        _ ≤ cpN i * (7 - cpF i) := Nat.mul_le_mul_right _ hk
    have hc := levK_sound hlev _ hs
    unfold chkK at hc
    have hdiv : (k * (7 - cpF i) + jj) / (7 - cpF i) = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hjj, Nat.zero_add]
    have hmod : (k * (7 - cpF i) + jj) % (7 - cpF i) = jj := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjj]
    simp only [Nat.zero_add, hdiv, hmod] at hc
    obtain ⟨hb, he⟩ := andB_true hc
    have hb' := Eq.mp Nat.blt_eq hb
    have hp : D.toArray[k * (7 - cpF i) + jj]! = D[k * (7 - cpF i) + jj] := by
      rw [get!_toArray, List.getD_eq_getElem]
    rw [hp]
    refine ⟨hb', ?_⟩
    rw [ss_get (by omega), getL_G7 (by omega), tm_get (i := i) (k := k) (fun _ => hk),
      tm_get (i := i) (k := D[k * (7 - cpF i) + jj] % cpN i) (fun _ => Nat.mod_lt _ (cpN_pos i)),
      tm_get (i := i + 1) (k := D[k * (7 - cpF i) + jj] / cpN i % cpN (i + 1))
        (fun _ => Nat.mod_lt _ (cpN_pos (i + 1))),
      tm_get (i := i + 2) (k := D[k * (7 - cpF i) + jj] / cpN i / cpN (i + 1)) (fun _ => hb'),
      mul_unpackW, mul_unpackW, mul_unpackW]
    exact beq_of_eqK he

open Certificates in
open CFSG.EvenSporadicStandard.Co1Pair in
theorem c27202 : cpOK = true := by
  obtain ⟨_, hSW, h0, h1, h2, hD0, hD1, hD2, hh0, hh1, hh2⟩ := lens
  have l0 : cpLevelOK 0 = true := level_ok (i := 0) (by decide) cptw0 dec0_eq h0 hh0 kT0 hD0 kL0
    (by decide)
  have l1 : cpLevelOK 1 = true := level_ok (i := 1) (by decide) cptw1 dec1_eq h1 hh1 kT1 hD1 kL1
    (by decide)
  have l2 : cpLevelOK 2 = true := level_ok (i := 2) (by decide) cptw2 dec2_eq h2 hh2 kT2 hD2 kL2
    (by decide)
  have ha : T.SW.toArray.all (fun w => w.all (· < 2)) = true := by
    rw [Array.all_eq_true]
    intro s hs
    have hs' : s < T.SW.length := by simpa using hs
    have hw := (wordsK_sound kS s hs').1
    simp only [List.getElem_toArray, List.all_eq_true, decide_eq_true_eq]
    exact fun l hl => (hw l hl).2
  rw [cpOK, ss_eq, l0, l1, l2, ha]
  simp [hSW]

end CertificateChecks.KernelCo1B.Pair27202

end
