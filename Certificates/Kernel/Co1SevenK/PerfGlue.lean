module

public import Certificates.Kernel.Co1SevenK.Perf
public import Certificates.Kernel.Co1SevenK.SylGlue

public section

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KS.SporSch.M24 CFSG.KS.SporSch.M24.MatL CFSG.Sporadic.Co1Schreier.Native
  Timmesfeld.Co1Seven Timmesfeld.Co1SevenPerfect

local notation "U" => CFSG.KS.Raw.unpack 24 24

theorem dag_rowsL : gDag aR bR = (rowsL D.M D.N, rowsL D.MI D.N, true) := dag_eq

theorem word_U {w : List Int} (h1 : lettersK D.N (encW w) = true) (h2 : decWord (encW w) = w) :
    word (rowsL D.M D.N) (rowsL D.MI D.N) w = U (wordWK D.M D.MI (encW w)) := by
  have e := word_eq_wordWK (M := D.M) (MI := D.MI) h1
  rw [h2] at e
  exact e

theorem perfKAt_word {T i : Nat} (h : perfKAt D.M D.MI D.N T i = true) :
    word (rowsL D.M D.N) (rowsL D.MI D.N) sWords[i]! = U (wordWK D.M D.MI (encW sWords[i]!)) := by
  unfold perfKAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact word_U h.1.1.1.1.1.2 h.1.1.1.2

theorem rowAt_T : rowAt (rowsL D.M D.N) iT = U (D.M iT) := by
  have e := rowAt_iT
  rw [dag_rowsL] at e
  exact e

theorem perfAt_K {i : Nat} (h : perfKAt D.M D.MI D.N (D.M iT) i = true) :
    (decide ((sIdx[i]!).1 < 6) && decide ((sIdx[i]!).2 < 6) &&
      perfAt (rowsL D.M D.N) (rowsL D.MI D.N) i) = true := by
  have hw := perfKAt_word h
  unfold perfKAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hj, hk⟩, hok⟩, -⟩, hl2⟩, -⟩, hd2⟩, hc⟩, he⟩ := h
  have hcw := word_U hl2 hd2
  unfold commW at hcw
  unfold perfAt
  dsimp only
  rw [rowAt_T, hw, hcw, hj, hk, hok, mul_unpackW, mul_unpackW, Nat.eq_of_beq_eq_true hc,
    Nat.eq_of_beq_eq_true he]
  simp [commW]

theorem co1PerfOK_K : co1PerfOK aR bR = true := by
  have hK := kPerf
  unfold perfK at hK
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range] at hK
  obtain ⟨h0, hall⟩ := hK
  unfold co1PerfOK
  dsimp only
  rw [dag_rowsL]
  dsimp only
  rw [perfKAt_word (hall 0 (by decide)), Bool.true_and, Bool.and_eq_true, Bool.and_eq_true,
    List.all_eq_true]
  refine ⟨⟨validRows_U _, ?_⟩, fun i hi => perfAt_K (hall i (List.mem_range.1 hi))⟩
  rw [bne_iff_ne, ne_eq]
  intro e
  rw [eqU_one_of e] at h0
  exact Bool.noConfusion h0

end CertificateChecks.KernelCo1SevenK

end
