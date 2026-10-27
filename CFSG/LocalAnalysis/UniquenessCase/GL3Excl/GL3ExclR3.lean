module

public import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclR3Basic
public import CFSG.RankThree.SubgroupLists.IrreducibleGL3
import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclOmega
import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclCoprime
import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclCyclic
import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclExtra
import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclMono
public import CFSG.LocalAnalysis.UniquenessCase.GL3Excl.GL3ExclBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.GL3Excl

private theorem not_dvd_of_eleven_le {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (a b c d : ℕ) :
    ¬ p ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d := by
  have key : ∀ {q k : ℕ}, 0 < q → q ≤ 7 → p ∣ q ^ k → False := fun hq hq7 h =>
    absurd (Nat.le_of_dvd hq (hp.dvd_of_dvd_pow h)) (by omega)
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact key (by norm_num) (by norm_num) h
      · exact key (by norm_num) (by norm_num) h
    · exact key (by norm_num) (by norm_num) h
  · exact key (by norm_num) (by norm_num) h

theorem gl3ExclR3_holds :
    GL3ExclR3 := by
  intro r p _ hp hp11 hr7 W H hW hHW hemb hr hstab t₁ ht₁ ht₁d t₂ ht₂ ht₂d y hy hyp α hyd hyns
  have hr2 : r ≠ 2 := by omega
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨K, hKW, hnorm, hK, hcases⟩ :=
    CFSG.RankThree.SubgroupLists.bloom_mitchell_irreducible_gl_three hr2 hW
  rcases hcases with hSL | ⟨M, hMt, hM, rfl⟩ | ⟨e, -, hprod, -⟩ | ⟨e, -⟩ |
    ⟨hperf, -, e, -⟩ | ⟨hcyc, -, -⟩ | ⟨hcard, hext, -⟩ | ⟨rfl, hmono⟩
  · exact hr (dvd_card_of_statedSL_le (hSL ▸ hKW) hstab)
  · exact false_of_omegaGL hr7 hpodd hMt hM hnorm (hHW ht₁) ht₁d (hHW ht₂) ht₂d (hHW hy) hyp hyd
      hyns
  · exact false_of_alternating_five_of_coprime hp
      (by simpa using not_dvd_of_eleven_le hp hp11 2 1 1 0) hKW hK e hprod (hHW hy) hyp hyd hyns
  · exact false_of_gl_three_two_of_coprime hp
      (by simpa using not_dvd_of_eleven_le hp hp11 4 1 0 1) hnorm hK e (hHW hy) hyp hyd hyns
  · exact false_of_three_alt_six_of_coprime hp
      (by simpa using not_dvd_of_eleven_le hp hp11 5 2 1 0) hnorm hK hperf e (hHW hy) hyp hyd
      hyns
  · exact false_of_isCyclic hr2 hnorm hK hcyc (hHW ht₁) ht₁d
  · exact false_of_extraspecial hr2 hnorm hK hcard hext (hHW ht₁) ht₁d (hHW ht₂) ht₂d
  · exact false_of_isTransitiveMonomial hr2 hp hp2 hmono hemb (hHW ht₁) ht₁d (hHW hy) hyp
      hyd hyns

end CFSG.LocalAnalysis.UniquenessCase.GL3Excl
