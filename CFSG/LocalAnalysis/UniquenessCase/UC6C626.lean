module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C626Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6S29

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf exists_isSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem ne_bot_of_one_le_pRank_uc6 {p : ℕ} (hp : p.Prime) {Q : Subgroup G}
    (hQ : 1 ≤ CFSG.Open.pRank p Q) : Q ≠ ⊥ := by
  rintro rfl
  obtain ⟨E, hE, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊥ : Subgroup G)
  have h1 : 1 ≤ CFSG.Open.pRank p (⊥ : Subgroup G) := hQ
  rw [le_bot_iff.mp hE, Subgroup.card_bot] at hcard
  exact (Nat.one_lt_pow (by omega) hp.one_lt).ne' hcard.symm

theorem c626_of_kernels (hgen : m.C626gen) (h619 : m.C619) : m.C626 := by
  intro p hp hdvd
  have hpp : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨P, hP⟩ := exists_isSylowOf p (m.M ⊓ normalizer (m.Z : Set G))
  have hPne : P ≠ ⊥ := by
    intro hbot
    have h1 := hP.card_eq
    rw [hbot, Subgroup.card_bot] at h1
    have hpos : Nat.card ↥(m.M ⊓ normalizer (m.Z : Set G)) ≠ 0 := Nat.card_pos.ne'
    have h2 := (hpp.dvd_iff_one_le_factorization hpos).1 hdvd
    have h3 : p ^ 1 ≤ p ^ (Nat.card ↥(m.M ⊓ normalizer (m.Z : Set G))).factorization p :=
      Nat.pow_le_pow_right hpp.pos h2
    rw [← h1, pow_one] at h3
    have := hpp.one_lt
    omega
  have hL := hgen p hp P hP hPne
  have hPM : P ≤ m.M := hP.le.trans inf_le_left
  have hstrong : IsStronglyPEmbedded p m.M :=
    isStronglyPEmbedded_of_sigmaOne m.hU m.S.maxLocal hp (m.hσ1 hp)
  have h1 : gammaL m.L p P ≤ m.M := by
    refine iSup_le fun Q => iSup_le fun hQP => iSup_le fun hQ1 => ?_
    refine inf_le_right.trans ?_
    exact hstrong.normalizer_le (ne_bot_of_one_le_pRank_uc6 hpp hQ1)
      (hP.isPGroup.of_injective (Subgroup.inclusion hQP) (Subgroup.inclusion_injective hQP))
      (hQP.trans hPM)
  have h2 : gammaL m.L m.r m.E ≤ m.M := by
    refine le_trans ?_ m.d.E_gamma
    refine iSup_le fun Q => iSup_le fun hQE => iSup_le fun hQ1 => ?_
    refine inf_le_right.trans ?_
    exact le_sSup ⟨Q, hQE, hQ1, rfl⟩
  have hLM : m.L ≤ m.M := hL.trans (sup_le h1 h2)
  have hHM : m.H ≤ m.M := by
    rw [h619]
    exact sup_le hLM inf_le_right
  exact m.hZ.not_le hHM

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
