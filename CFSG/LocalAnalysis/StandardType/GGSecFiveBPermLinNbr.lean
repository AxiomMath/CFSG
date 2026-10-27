module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLinNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseRows
import CFSG.LocalAnalysis.StandardType.GGClassicalCentralImageLabel
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLSchur
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal

section Rows


theorem ggSecFiveBPermLinNbrInput_of_label (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hTPn : GGNbrTablePNbrInputNarrow) (hA8 : GGForkA8NotReflInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput) (hFC : GGResNbrFixCentralizesInput)
    (hKlab : GGSecFiveBPermLinNbrLabelInput) (hSU : GGSecFiveBPermLinSU6Input) :
    GGSecFiveBPermLinNbrInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hT1 n e hpres hn eta hEta hLA hG0 hB hlab
  obtain ⟨lab, hΛ, hLin, hlabL, hLab'⟩ := hlab.exists_label_eq
  rcases lab with ⟨tag, rank, f⟩
  obtain ⟨htag, hrank, hpdvd⟩ := hLin
  subst htag
  subst hrank
  obtain ⟨hp, -, -⟩ := (hR.1.1.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hf2 : 2 ≤ f := by
    have h1 : 1 ≤ f := hΛ.1
    by_contra h
    have hf1 : f = 1 := by omega
    rw [hf1] at hpdvd
    norm_num at hpdvd
    exact hp.ne_one hpdvd
  obtain ⟨ψ, hψker, hψrange⟩ := exists_sl_centralImage_of_hasLabel hlab.1 hn hf2 hlabL
  have hLabf : GGInnerDiagOnLabel
      (fun p lab' => GGSecFiveBPermLinLabel n p lab' ∧ lab'.n = f) p Bs L :=
    largeEvenMarking_mono (fun lab' R _ I F θ h' => ⟨⟨h'.1.1, by rw [h'.1.2]⟩, h'.2⟩) hLab'
  obtain ⟨K, hK𝒦, i0, hKA⟩ := hR.exists_mem_bCoordinateBlock hX hTCJ hRig hTPn hA8 hraw
    hiso hFC hB (by omega) eta hEta hLA
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK𝒦
  have hKqs : CFSG.Assembly.IsQuasisimple K :=
    isQuasisimple_of_largeEvenMarking (hR.1.2.2.1.2 y K hnb)
  obtain ⟨labK, hKl, hcase⟩ := hKlab G p B Bs x L D J 𝒦 hR hT1 n e hpres hn eta hEta hLA
    hG0 hB f hf2 hLabf K hK𝒦 i0 hKA
  rcases hcase with hC | hB' | hD | ⟨hp3, hf3, hA⟩ | ⟨hn4, a, hf, ha2, hpa, htA⟩
  · rw [hC] at hKl
    exact Or.inl ⟨f, K, i0, hf2, hK𝒦, ⟨ψ, hψker, hψrange⟩,
      nonempty_mulEquiv_statedSp_of_hasLabel hKqs.1 (by omega) hf2 (Or.inr hKl), hKA⟩
  · rw [hB'] at hKl
    exact Or.inl ⟨f, K, i0, hf2, hK𝒦, ⟨ψ, hψker, hψrange⟩,
      nonempty_mulEquiv_statedSp_of_hasLabel hKqs.1 (by omega) hf2 (Or.inl hKl), hKA⟩
  · rw [hD] at hKl
    exact Or.inr (Or.inl ⟨f, K, i0, hf2, hK𝒦, ⟨ψ, hψker, hψrange⟩,
      nonempty_mulEquiv_spinMinus_of_hasLabel hKqs.1 hn hf2 hKl, hKA⟩)
  · subst hf3
    rcases hA with hA | hA
    · rw [hA] at hKl
      obtain ⟨-, ⟨eA⟩⟩ := ggKSL_sl_of_hasLabel hKqs.1 hKqs.2 (r := 2 * n - 3) (by omega) hKl
      exact Or.inr (Or.inr (Or.inl ⟨2 * n - 3 + 1, K, i0, hp3, Or.inl (by omega), hK𝒦,
        ⟨ψ, hψker, hψrange⟩,
        ⟨eA.trans (specialLinearGroupEquivStatedSL (2 * n - 3 + 1) (ZMod 2)).symm⟩, hKA⟩))
    · rw [hA] at hKl
      obtain ⟨-, ⟨eA⟩⟩ := ggKSL_sl_of_hasLabel hKqs.1 hKqs.2 (r := 2 * n - 2) (by omega) hKl
      exact Or.inr (Or.inr (Or.inl ⟨2 * n - 2 + 1, K, i0, hp3, Or.inr (by omega), hK𝒦,
        ⟨ψ, hψker, hψrange⟩,
        ⟨eA.trans (specialLinearGroupEquivStatedSL (2 * n - 2 + 1) (ZMod 2)).symm⟩, hKA⟩))
  · subst hn4
    subst hf
    rw [htA] at hKl
    exact Or.inr (Or.inr (Or.inr ⟨a, K, i0, rfl, ha2, hpa, hK𝒦, ⟨ψ, hψker, hψrange⟩,
      hSU G p B Bs x L D J 𝒦 hR hT1 e hpres eta hEta hLA hG0 hB a ha2 hpa hLabf
        K hK𝒦 i0 hKA hKl, hKA⟩))

end Rows

end CFSG.StandardType

end
