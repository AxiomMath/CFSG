module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcDich
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcG2derVac
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcSzVac
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcTitsVac
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcReeVac
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU1Untw
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU1TwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU1TriD4
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU4
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU2
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcU3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggNbrLSideRSExcU1_holds
    : GGNbrLSideRSExcU1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ggNbrLSideRSExc_u1_untw
  exact ⟨h1, h2, h3, h4, h5, ggNbrLSideRSExc_u1_twE6, ggNbrLSideRSExc_u1_triD4⟩

theorem ggNbrLSideExcUntwData_of_u1
    (hLD : GGNbrLSideRSExcLangDich) (hU1 : GGNbrLSideRSExcU1) : GGNbrLSideExcUntwData := by
  obtain ⟨hG2, hF4, hE6, hE7, hE8, -, -⟩ := hU1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro lab ht K _ _ hlab _ hK
    have hn : 2 ≤ lab.n := by
      have h := hlab.2
      rw [ht] at h
      exact h.2
    exact ggNbrLSideDich_of_transport hLD
      (fun _ => (by norm_num : 4 = 2 ^ 2).le.trans (Nat.pow_le_pow_right (by norm_num) hn))
      (by unfold ggNbrLSideRank; rw [ht]; rfl) (hG2 K lab.n hn hK)
  · intro lab ht K _ _ hlab _ hK
    exact ggNbrLSideDich_of_noPSL3 (ggNbrLSideNoPSL3_g2der hK)
  · intro lab ht K _ _ hlab _ hK
    exact ggNbrLSideDich_of_transport hLD (fun h => by cases h)
      (by unfold ggNbrLSideRank; rw [ht]; rfl) (hF4 K lab.n hlab.1 hK)
  · intro lab ht K _ _ hlab _ hK
    exact ggNbrLSideDich_of_transport hLD (fun h => by cases h)
      (by unfold ggNbrLSideRank; rw [ht]; rfl) (hE6 K lab.n hlab.1 hK)
  · intro lab ht K _ _ hlab _ hK
    exact ggNbrLSideDich_of_transport hLD (fun h => by cases h)
      (by unfold ggNbrLSideRank; rw [ht]; rfl) (hE7 K lab.n hlab.1 hK)
  · intro lab ht K _ _ hlab _ hK
    exact ggNbrLSideDich_of_transport hLD (fun h => by cases h)
      (by unfold ggNbrLSideRank; rw [ht]; rfl) (hE8 K lab.n hlab.1 hK)

theorem ggNbrLSideExcTwData_of_u1
    (hLD : GGNbrLSideRSExcLangDich) (hU1 : GGNbrLSideRSExcU1) : GGNbrLSideExcTwData := by
  obtain ⟨-, -, -, -, -, hE6, hD4⟩ := hU1
  refine ⟨?_, ?_⟩
  · intro lab ht K _ _ hlab _ hK
    exact ggNbrLSideDich_of_transport hLD (fun h => by cases h)
      (by unfold ggNbrLSideRank; rw [ht]; rfl) (hE6 K lab.n hlab.1 hK)
  · intro lab ht K _ _ hlab _ hK
    exact ggNbrLSideDich_of_transport hLD (fun h => by cases h)
      (by unfold ggNbrLSideRank; rw [ht]; rfl) (hD4 K lab.n hlab.1 hK)

theorem ggNbrLSideSuzukiReeData_of_excl
    (hDet : GGNbrLSideClsDet) (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    GGNbrLSideSuzukiReeData := by
  refine ⟨?_, ?_⟩
  · intro lab _ K _ _ _ _ hK
    exact ggNbrLSideDich_of_noPSL3 (ggNbrLSideNoPSL3_twB2 hK)
  · intro lab ht K _ _ hlab _ hK
    rcases ht with ht | ht
    · have h3 : 3 ≤ lab.n := by
        have h := hlab.2
        rw [ht] at h
        exact h.2.2
      exact ggNbrLSideDich_of_noPSL3
        (ggNbrLSideNoPSL3_twF4 hDet hO (by omega : 1 ≤ (lab.n - 1) / 2) hK)
    · have h1 : lab.n = 1 := by
        have h := hlab.2
        rw [ht] at h
        exact h.2
      have key : ∀ {a : ℕ}, a = 0 → Nat.card K = 2 ^ (2 * a + 1) →
          GGNbrLSideDich lab (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K)) := by
        intro a ha hKa
        subst ha
        exact ggNbrLSideDich_of_noPSL3 (ggNbrLSideNoPSL3_twF4der (by simpa using hKa))
      exact key (by omega) hK

theorem ggNbrLSideExcUntwData_holds
    : GGNbrLSideExcUntwData :=
  ggNbrLSideExcUntwData_of_u1
    (ggNbrLSideRSExc_langDich_of_U234 ggNbrLSideRSExcU2_holds
      (ggNbrLSideRSExc_u3_of_u2 ggNbrLSideRSExcU2_holds) ggNbrLSideRSExc_u4)
    ggNbrLSideRSExcU1_holds

theorem ggNbrLSideExcTwData_holds
    : GGNbrLSideExcTwData :=
  ggNbrLSideExcTwData_of_u1
    (ggNbrLSideRSExc_langDich_of_U234 ggNbrLSideRSExcU2_holds
      (ggNbrLSideRSExc_u3_of_u2 ggNbrLSideRSExcU2_holds) ggNbrLSideRSExc_u4)
    ggNbrLSideRSExcU1_holds

theorem ggNbrLSideSuzukiReeData_holds
    : GGNbrLSideSuzukiReeData :=
  ggNbrLSideSuzukiReeData_of_excl CFSG.LocalAnalysis.GLTheoremA.cls_det
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput

end CFSG.StandardType

end
