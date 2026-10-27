module

public import CFSG.Assembly.Defs
public import CFSG.Monster.B.Co2.PermArr
public import Certificates.Data.D4HexGeoCheck

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.D4Hex CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem hexPtLocalOK_spec {pts ptL : Array ℕ} {G : Array (Array ℕ)} {lay : Array ℕ} {b0 : ℕ}
    {hW pW : List String} {H P : Array (Array ℕ)} (hH : H = hexWordArrs G hW)
    (hP : P = hexWordArrs G pW) (h : hexPtLocalOK pts ptL G lay b0 hW pW = true) :
    hexWordsOK G.size hW = true ∧ hexWordsOK G.size pW = true ∧ b0 < 819 ∧ lay[b0]! = 6 ∧
      ((List.range 9).map fun k => ptL[k]!).Nodup ∧ (∀ i < H.size, (H[i]!)[0]! = 0) ∧
      orbOKR 3276 H.size (fun j y x => hexActOK pts H[j]! y x) b0 512 (fun x => lay[x]! == 6)
        (orbBFS 3276 H.size (hexActS pts (hexLineKeyMap pts) H) b0) = true ∧
      (∀ i < P.size, (P[i]!)[0]! = 0 ∧ (P[i]!)[b0]! = b0) ∧
      ∀ a < 9, ∀ b < 9, a ≠ b → ∃ i < P.size,
        hexActOK pts P[i]! (819 + ptL[0]!) (819 + ptL[a]!) = true ∧
        hexActOK pts P[i]! (819 + ptL[1]!) (819 + ptL[b]!) = true := by
  subst hH hP
  unfold hexPtLocalOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun i hi => ?_, h7, fun i hi => ?_, fun a ha b hb hab => ?_⟩
  · have := allLt_spec h6 hi
    simpa using this
  · have := allLt_spec h8 hi
    simpa [Bool.and_eq_true] using this
  · have := h9 a ha b hb
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range] at this
    rcases this with h | ⟨i, hi, e⟩
    · exact absurd h hab
    · exact ⟨i, hi, by simpa [Bool.and_eq_true] using e⟩

theorem hexLnLocalOK_spec {pts : Array ℕ} {G : Array (Array ℕ)} {lay : Array ℕ} {y0 m0 : ℕ}
    {nW tW : List String} {Nn T : Array (Array ℕ)} (hN : Nn = hexWordArrs G nW)
    (hT : T = hexWordArrs G tW) (h : hexLnLocalOK pts G lay y0 m0 nW tW = true) :
    hexWordsOK G.size nW = true ∧ hexWordsOK G.size tW = true ∧ y0 < 819 ∧ lay[y0]! = 5 ∧
      819 ≤ m0 ∧ m0 < 3276 ∧ lay[m0]! = 6 ∧ (∀ i < Nn.size, hexActOK pts Nn[i]! 819 819 = true) ∧
      orbOKR 3276 Nn.size (fun j y x => hexActOK pts Nn[j]! y x) y0 768 (fun x => lay[x]! == 5)
        (orbBFS 3276 Nn.size (hexActS pts (hexLineKeyMap pts) Nn) y0) = true ∧
      orbOKR 3276 Nn.size (fun j y x => hexActOK pts Nn[j]! y x) m0 2048 (fun x => lay[x]! == 6)
        (orbBFS 3276 Nn.size (hexActS pts (hexLineKeyMap pts) Nn) m0) = true ∧
      (∀ i < T.size, hexActOK pts T[i]! 819 819 = true ∧ hexActOK pts T[i]! m0 m0 = true) ∧
      ∀ a < 3, ∀ b < 3, a ≠ b → ∃ i < T.size, (T[i]!)[pts[0]!]! = pts[a]! ∧
        (T[i]!)[pts[1]!]! = pts[b]! := by
  subst hN hT
  unfold hexLnLocalOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun i hi => ?_, h9, h10, fun i hi => ?_,
    fun a ha b hb hab => ?_⟩
  · exact allLt_spec h8 hi
  · have := allLt_spec h11 hi
    simpa [Bool.and_eq_true] using this
  · have := h12 a ha b hb
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range] at this
    rcases this with h | ⟨i, hi, e⟩
    · exact absurd h hab
    · exact ⟨i, hi, by simpa [Bool.and_eq_true] using e⟩

theorem d4GeoCheck_spec {pts lay0 : Array ℕ} {G : Array (Array ℕ)}
    (h : d4GeoCheck pts lay0 G = true) :
    hexPtsOK pts = true ∧ hexIncOK pts (hexPtL pts) = true ∧ hexMeetOK pts (hexPtL pts) = true ∧
      pts[0]! = 0 ∧ G.size = 8 ∧ lay0.size = 819 ∧
      (∀ x < 819, lay0[x]! = ((hexLayBFS pts (hexPtL pts) 0).1)[x]!) ∧
      hexLayOK pts (hexPtL pts) 0 (hexLayBFS pts (hexPtL pts) 0).1
        (hexLayBFS pts (hexPtL pts) 0).2 = true ∧
      hexLayOK pts (hexPtL pts) 819 (hexLayBFS pts (hexPtL pts) 819).1
        (hexLayBFS pts (hexPtL pts) 819).2 = true ∧
      hexCycleOK pts (hexPtL pts) (hexMkCycle pts (hexPtL pts) 0) = true ∧
      hexLinesOK pts G = true ∧
      hexPtLocalOK pts (hexPtL pts) G (hexLayBFS pts (hexPtL pts) 0).1 hexB0 hexHWords
        hexPWords = true ∧
      hexLnLocalOK pts G (hexLayBFS pts (hexPtL pts) 819).1 hexY0 hexM0 hexNWords
        hexTWords = true := by
  unfold d4GeoCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun x hx => ?_, h8, h9, h10, h11, h12, h13⟩
  have := allLt_spec h7 hx
  simpa using this

end CFSG.Quasithin.D4Hex
