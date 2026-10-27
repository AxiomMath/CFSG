module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251o
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251p
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251f

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9 (R920odd)

variable {G : Type} [Group G] [Finite G]

@[expose] def S22_5_1RStar (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)),
    NbarSplit D Nb → ∀ i, D.k ≠ 1 → CFSG.Open.evenRank G = 3 →
      (¬ ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2) → (∀ j, j ≠ i → IsL2Ev ↥(Nb j) 1) →
      (∀ p ∈ D.sig, p ∣ Nat.card ↥(Nb i)) →
      (∀ p ∈ D.sig, CFSG.pRank p (MBar D.M D.U) = 2) →
      (∀ p ∈ D.sig, ∀ P : Subgroup G, P ≤ D.M → IsPGroup p ↥P →
        P ≤ normalizer (jOf D.T : Set G) → IsCyclic ↥(mbarImage D.M D.U P)) →
      False

theorem s22_5_1R3K2_of_rStar (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h119 : R119W D) (h17 : S21_17 D Ch) (h211 : S21_1 D Ch)
    (h2112 : S21_12 D Ch) (h31 : S22_3_1 D Ch) (h33 : S22_3_3 D Ch)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hSg : UC6S846.SigmaStd D)
    (h847 : R847E3L3 D) (h920 : R920odd D) (h923 : F09.R923 D) (h8107 : F08.R8107 D)
    (hR : S22_5_1RStar D Ch) : S22_5_1R3K2 D Ch := by
  intro hH c m Nb hNb i hk hσ
  by_contra hbad
  have hnsp : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := fun hsp =>
    hk (by unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam; rw [if_pos hsp])
  have hS3 := uc22p2251p_isL2Ev_one D Ch hx h61 h33 h119 h17 h211 h2112 hn3 hSg h847 h920 h923
    h8107 hnsp hH c hNb hbad hσ
  have hbad' : IsL2Ev ↥(Nb i) 2 ∨ IsL3 ↥(Nb i) 1 ∨ IsS5 ↥(Nb i) := by
    rcases hNb.2 i with ⟨n, hn⟩ | h | h
    · obtain rfl : n = 2 := by
        by_contra hne
        exact hbad ⟨n, hn, hne⟩
      exact Or.inl hn
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨K, hK, -⟩ := uc22p2251b_exists_bad D hx h61 h119 h17 hH c.toCtx22 hNb hbad
  have hp5 : ∀ p ∈ D.sig, 5 ≤ p := by
    intro p hp
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    have hp3 : p ≠ 3 := by
      rintro rfl
      exact hnsp (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hK) hp)
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hpp
    have h2 := hpp.two_le
    omega
  have hcyc : ∀ p ∈ D.sig, ∀ P : Subgroup G, P ≤ D.M → IsPGroup p ↥P →
      P ≤ normalizer (jOf D.T : Set G) → IsCyclic ↥(mbarImage D.M D.U P) := by
    intro p hp P hPM hPp hPJ
    by_contra hnc
    exact (h31 hH c).2 (P2251g.calCGS_le D h61 hp hPM hPp hPJ
      (uc22p2251f_le_centralizer D Ch h33 hH c hNb hS3 hbad' (D.sig_prime p hp).1 (hp5 p hp) hPM
        hPJ hPp) hnc)
  have hle : ∀ p ∈ D.sig, ¬ 2 < CFSG.pRank p (MBar D.M D.U) := by
    intro p hp hr
    obtain ⟨P, hPM, hPp, hPJ, hnc⟩ := P2251g.exists_noncyclic D (D.sig_prime p hp).1
      (P2251g.not_sq_dvd_card D hNb hS3 hbad (D.sig_prime p hp).1 (hp5 p hp)) hr
    exact hnc (hcyc p hp P hPM hPp hPJ)
  obtain ⟨p, hp⟩ := hSg.nonempty
  have he : CFSG.Open.evenRank G = 3 :=
    le_antisymm (not_lt.1 fun he =>
      hle p hp (uc22p2251a_two_lt_pRank_mbarU D hx h61 he c.toCtx22 p hp)) D.standing.rank
  have hrk : ∀ q ∈ D.sig, CFSG.pRank q (MBar D.M D.U) = 2 := fun q hq =>
    le_antisymm (not_lt.1 (hle q hq))
      (uc22p22n_one_lt_pRank_mbar D hx h61 (uc22p22e_inCalV_U D) c.hU q hq)
  exact hR hH c m Nb hNb i hk he hbad hS3 hσ hrk hcyc

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
