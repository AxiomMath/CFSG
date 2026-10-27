module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C632c
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C632d
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal
public import CFSG.LocalAnalysis.UniquenessCase.UC6C632c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem c632_of_kernels (hK : UCK.K35c) (h625 : m.C625) (h626 : m.C626) (h628b : m.C628b)
    (h631 : m.C631) : m.C632 := by
  classical
  have hcyc := m.sylow_cyclic_of_pRank_eq_one h625 (m.hr.odd_of_ne_two m.d.odd)
  have h629 := m.six29 h625 h626 h628b
  obtain ⟨p, hp⟩ := m.hk.nonempty
  have hpr : p.Prime := (Dat.sig_prime _ hp).1
  haveI : Fact p.Prime := ⟨hpr⟩
  have hp2 : p ≠ 2 := (Dat.sig_prime _ hp).2
  unfold C632
  rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
  intro B hBle hB1
  have hBr : B ≤ m.R := hBle.trans (inf_le_left.trans (sup_le m.hZ.le m.E_le_R))
  have hBne : B ≠ ⊥ := by
    intro hB0
    obtain ⟨E, hEB, -, hEcard⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained m.r m.hr B
    have hE1 : E = ⊥ := le_bot_iff.1 (hB0 ▸ hEB)
    rw [hE1, Subgroup.card_bot] at hEcard
    have h3 : m.r ^ 1 ≤ m.r ^ CFSG.Open.pRank m.r B := Nat.pow_le_pow_right m.hr.pos hB1
    have h2 := m.hr.two_le
    rw [← hEcard, pow_one] at h3
    omega
  by_contra hN
  have hXtop : normalizer (B : Set G) ≠ ⊤ := by
    intro hXt
    haveI := Dat.standing.simple
    have hBn : B.Normal :=
      ⟨fun n hn g => by
        have hg : g ∈ normalizer (B : Set G) := hXt ▸ Subgroup.mem_top g
        exact (mem_normalizer_iff.1 hg n).1 hn⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal B with h | h
    · exact hBne h
    · exact m.M_ne_top (top_le_iff.1 (h ▸ hBr.trans m.R_le_M))
  have hKX : CFSG.Open.IsKGroup ↥(normalizer (B : Set G)) := Dat.standing.kProper.isKGroup _ hXtop
  have hM := m.isStronglyPEmbedded_M hp
  have hdvd := m.dvd_card_inf_normalizer hp hcyc h626 h628b h631 hBle
  have hN' := isStronglyPEmbedded_inf hM hN hdvd
  have hrank := m.two_lt_pRank_normalizer hp hcyc h626 h628b h631 hBle
  have hsolv := hK ↥(normalizer (B : Set G)) hKX p hpr hp2 _ hN' hrank
  have hsolv' : CFSG.HallHigman.IsPSolvable p ↥(m.M ⊓ normalizer (B : Set G)) :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe inf_le_right) hsolv
  exact m.not_isPSolvable_inf_normalizer hp hcyc h626 h628b h629 h631 hBle hsolv'

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
