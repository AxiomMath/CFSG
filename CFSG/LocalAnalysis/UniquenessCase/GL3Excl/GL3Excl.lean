module

public import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclBasic
public import CFSG.RankThree.SubgroupLists.IrreducibleGL3
import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclOmega
import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclAlt
import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclCyclic
import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclExtra
import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclMono

public section

namespace CFSG.LocalAnalysis.UniquenessCase.GL3Excl

theorem gl3Excl_holds
    : GL3Excl := by
  intro r p _ hrp W H hW hHW hemb hr hstab t₁ ht₁ ht₁d t₂ ht₂ ht₂d y hy hyp α hyd hyns
  have hr2 : r ≠ 2 := by omega
  have hr7 : 7 ≤ r := by omega
  have hpodd : Odd p := by rcases hrp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hpp : p.Prime := by rcases hrp with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  obtain ⟨K, hKW, hnorm, hK, hcases⟩ :=
    CFSG.RankThree.SubgroupLists.bloom_mitchell_irreducible_gl_three hr2 hW
  rcases hcases with hSL | ⟨M, hMt, hM, rfl⟩ | ⟨e, hmod, hprod, -⟩ | ⟨-, hmod⟩ |
    ⟨hperf, -, e, hmod⟩ | ⟨hcyc, -, -⟩ | ⟨hcard, hext, -⟩ | ⟨rfl, hmono⟩
  · exact hr (dvd_card_of_statedSL_le (hSL ▸ hKW) hstab)
  · exact false_of_omegaGL hr7 hpodd hMt hM hnorm (hHW ht₁) ht₁d (hHW ht₂) ht₂d (hHW hy) hyp hyd
      hyns
  · obtain ⟨rfl, rfl⟩ : r = 31 ∧ p = 5 := by omega
    exact false_of_alternating_five hr2 hKW hK e hprod (hHW ht₁) ht₁d (hHW hy) hyp hyd hyns
  · omega
  · obtain ⟨rfl, rfl⟩ : r = 31 ∧ p = 5 := by omega
    exact false_of_three_alt_six hr2 hnorm hK hperf e (hHW ht₁) ht₁d (hHW ht₂) ht₂d (hHW hy) hyp
      hyd hyns
  · exact false_of_isCyclic hr2 hnorm hK hcyc (hHW ht₁) ht₁d
  · exact false_of_extraspecial hr2 hnorm hK hcard hext (hHW ht₁) ht₁d (hHW ht₂) ht₂d
  · exact false_of_isTransitiveMonomial hr2 hpp (by omega) hmono hemb (hHW ht₁) ht₁d (hHW hy) hyp
      hyd hyns

end CFSG.LocalAnalysis.UniquenessCase.GL3Excl
