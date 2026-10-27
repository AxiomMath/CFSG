module

public import CFSG.LocalAnalysis.StandardType.TitsOvergroupCoverSound
public import CFSG.LocalAnalysis.StandardType.TitsOvergroupPairSound

public section

namespace CFSG.StandardType.TitsOvergroup

open CFSG.StandardType.SylowPair

variable {D : PairData} {S : List (Equiv.Perm (Fin D.n))}

theorem pairCheck_parts (h : pairCheck D = true) :
    checkInv D = true ∧ checkP D = true ∧ checkN D = true ∧ checkNormal D = true ∧
      checkSide D = true ∧ checkCover D = true ∧ checkGen D = true ∧ checkSideMem D = true := by
  simp only [pairCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem dichotomy (hS : Sound D S) (hcheck : pairCheck D = true)
    {Y : Subgroup (Equiv.Perm (Fin D.n))} (hPY : pairP D S ≤ Y) (hYG : Y ≤ pairG D S)
    (hY : Y ≠ pairG D S) {y : Equiv.Perm (Fin D.n)} (hy : y ∈ Y) :
    y ∈ pairN D S ∨ ∃ i < D.repW.length, D.kind[i]! ≠ 0 ∧
      y ∈ CFSG.AGLEmbedding.MaxD2.dcoset (pairN D S) ((pairReps D S).getD (i + 1) 1) ∧
      ∃ a ∈ pairN D S, (pairClosure (pairP D S) ((pairReps D S).getD (i + 1) 1)).map
        (MulAut.conj a).toMonoidHom ≤ Y := by
  obtain ⟨hInv, hP, hN, hNorm, hSide, hCover, hGen, hMem⟩ := pairCheck_parts hcheck
  have hNP := pairN_le_normalizer hS hP hNorm
  obtain ⟨i, hi, a, ha, b, hb, hyi⟩ := exists_dcoset_pair hS hN hCover y (hYG hy)
  rcases i with _ | i
  · left
    have h1 : (pairReps D S).getD 0 1 = 1 := by simp [pairReps]
    rw [h1, mul_one] at hyi
    rw [hyi]
    exact (pairN D S).mul_mem ha hb
  · right
    have hi' : i < D.repW.length := by omega
    have hle := conj_pairClosure_le hNP hPY ha hb hy hyi
    by_cases hk : D.kind[i]! = 0
    · exfalso
      have hG := pairG_le_pairClosure hS (invsOK_of_checkCover hCover) hGen hi' hk
      have hmap := (Subgroup.map_mono (f := (MulAut.conj a).toMonoidHom) hG).trans hle
      apply hY
      refine le_antisymm hYG fun x hx => ?_
      have haG : a ∈ pairG D S := pairN_le_pairG ha
      refine hmap ⟨a⁻¹ * x * a, ?_, ?_⟩
      · exact (pairG D S).mul_mem ((pairG D S).mul_mem ((pairG D S).inv_mem haG) hx) haG
      · simp [MulAut.conj_apply, mul_assoc]
    · exact ⟨i, hi', hk, ⟨a, ha, b, hb, hyi⟩, a, ha, hle⟩

end CFSG.StandardType.TitsOvergroup
