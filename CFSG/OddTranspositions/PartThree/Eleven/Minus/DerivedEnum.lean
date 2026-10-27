module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.DerivedCheck

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

theorem enumOK_enumerates {n : ℕ} {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (hsize : ∀ i < c.pts.size, (c.pts[i]!).size = n)
    (h : enumOK n gs ps c = true) :
    Enumerates (Subgroup.closure (permsA n gs)) c.pts.toList := by
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps h
  simp only [CFSG.RankThree.Native.enumOK, Bool.and_eq_true] at h
  obtain ⟨-, hc⟩ := h
  have key_eq : ∀ {i j : ℕ}, i < c.pts.size → j < c.pts.size →
      c.pts[i]! = c.pts[j]! → i = j := fun hi hj hij =>
    arrCertOK_keys_inj hc hi hj (by rw [hij])
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi, hti⟩ := List.getElem_of_mem ht
    have hi' : i < c.pts.size := by simpa using hi
    have ht' : t = c.pts[i]! := by
      rw [← hti, getElem!_pos c.pts i hi']
      exact Array.getElem_toList (xs := c.pts) (i := i) hi
    refine ⟨permOfArr n t, (hmem _).2 ⟨i, hi', ?_⟩, ?_⟩
    · rw [ht']
    · rw [ht']
      exact ⟨hsize i hi', rep_of_validA (hval i hi')⟩
  · intro g hg
    obtain ⟨i, hi, he⟩ := (hmem g).1 hg
    refine ⟨c.pts[i]!, ?_, ?_⟩
    · rw [getElem!_pos c.pts i hi]
      exact Array.mem_toList_iff.2 (Array.getElem_mem hi)
    · rw [← he]
      exact ⟨hsize i hi, rep_of_validA (hval i hi)⟩
  · rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hi' : i.1 < c.pts.size := by simpa using i.2
    have hj' : j.1 < c.pts.size := by simpa using j.2
    have harr : c.pts[i.1]! = c.pts[j.1]! := by
      have h' := hij
      simp only [Array.getElem_toList] at h'
      rw [← getElem!_pos c.pts i.1 hi', ← getElem!_pos c.pts j.1 hj'] at h'
      exact h'
    exact Fin.ext (key_eq hi' hj' harr)

end CFSG.OddTranspositions.PartThree
