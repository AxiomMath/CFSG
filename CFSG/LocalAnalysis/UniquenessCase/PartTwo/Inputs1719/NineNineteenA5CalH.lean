module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Cyc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5Opp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5Weak
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5Cyc
import CFSG.LocalAnalysis.UniquenessCase.UC6N588A1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs14
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem mem_calH9 {D : Data G} (h71 : F07.R71 D) (hK : UCK.K332Cyc)
    (hsp5 : IsStronglyPEmbedded 5 D.M) {L D₃ Y H : Subgroup G}
    (h3 : CFSG.Open.pRank 3 (H ⊓ D.M) ≤ 3) (hyp : PartTwo.Hyp919c D L D₃ Y H) (hA5 : IsAlt (Bar2 L) 5) (hLY : L ≤ Y)
    (hH2 : pCoreOf 2 H ≠ ⊥) : H ∈ F09.calH9 D Y := by
  have hyp' := hyp
  obtain ⟨hL, hD₃L, hD₃, hD₃U, hYM, hLeq, hnorm, hidx, hHtop, hYH, hHM⟩ := hyp
  simp only [F09.calH9, Set.mem_setOf_eq]
  refine ⟨hYH, hHM, ?_⟩
  have hLYinf : L ⊓ Y = L := inf_eq_left.2 hLY
  have hnorm' : (L.subgroupOf Y).Normal := by rwa [hLYinf] at hnorm
  have hidx' : ∃ k : ℕ, (L.subgroupOf Y).index = 2 ^ k := by rwa [hLYinf] at hidx
  have hOpp : Opp 3 Y = L := opp_three_eq_of_le hL hA5 hLY hnorm' hidx'
  rw [hOpp]
  obtain ⟨P, hP, hD₃P, hPM, hwc, Q, hQgrp, φ, hQ, hφ⟩ :=
    exists_sylow_weaklyClosed h71 hsp5 hyp' hA5 hLY hH2
  have hHK : CFSG.Open.IsKGroup ↥H := D.standing.kProper.isKGroup H hHtop
  have hP3 : CFSG.Open.pRank 3 P ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) (le_inf hP.le hPM)).trans h3
  have hrank : CFSG.Open.pRank 3 (⨆ h : ↥H, D₃.map (MulAut.conj (h : G)).toMonoidHom) = 1 :=
    pRank_iSup_map_conj_eq_one hK hHK hP hP3 hD₃P hD₃ hwc hQ φ fun x hx => hφ x (hD₃L hx)
  have hLe : (⨆ h : ↥H, L.map (MulAut.conj (h : G)).toMonoidHom) ≤
      ⨆ h : ↥H, D₃.map (MulAut.conj (h : G)).toMonoidHom := by
    refine iSup_le fun h => ?_
    have hstep : L.map (MulAut.conj (h : G)).toMonoidHom ≤
        (⨆ l : ↥L, D₃.map (MulAut.conj (l : G)).toMonoidHom).map
          (MulAut.conj (h : G)).toMonoidHom :=
      Subgroup.map_mono (le_iSup_map_conj hL hA5 hD₃L hD₃)
    rw [Subgroup.map_iSup] at hstep
    refine le_trans hstep (iSup_le fun l => ?_)
    have hlH : (h : G) * (l : G) ∈ H := H.mul_mem h.2 (hYH (hLY l.2))
    have hconj : (D₃.map (MulAut.conj (l : G)).toMonoidHom).map
        (MulAut.conj (h : G)).toMonoidHom =
        D₃.map (MulAut.conj ((⟨(h : G) * (l : G), hlH⟩ : ↥H) : G)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hconj]
    exact le_iSup (fun k : ↥H => D₃.map (MulAut.conj (k : G)).toMonoidHom)
      ⟨(h : G) * (l : G), hlH⟩
  have hD₃le : D₃ ≤ ⨆ h : ↥H, L.map (MulAut.conj (h : G)).toMonoidHom := by
    have h1 : L.map (MulAut.conj ((1 : ↥H) : G)).toMonoidHom = L := by
      have hc : MulAut.conj ((1 : ↥H) : G) = 1 := map_one _
      rw [hc]
      exact Subgroup.map_id L
    calc D₃ ≤ L := hD₃L
      _ = L.map (MulAut.conj ((1 : ↥H) : G)).toMonoidHom := h1.symm
      _ ≤ ⨆ h : ↥H, L.map (MulAut.conj (h : G)).toMonoidHom :=
        le_iSup (fun h : ↥H => L.map (MulAut.conj (h : G)).toMonoidHom) 1
  refine le_antisymm ?_ ?_
  · refine (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hLe).trans_eq hrank
  · exact UCK.N588A.one_le_pRank Nat.prime_three hD₃le hD₃

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineNineteenA5
