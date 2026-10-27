module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251g
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251f
import CFSG.LocalAnalysis.UniquenessCase.UC22KBar
import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ya
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.RankThree.PartOne.S11c.Simple168
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.LocalAnalysis.UniquenessCase.UC22P22xh
import CFSG.RankThree.PartOne.S11c.OuterInner
import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)

variable {G : Type} [Group G] [Finite G]

theorem P2251n.not_dvd_card_of_not_dvd (D : Data G) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hS3 : ∀ k, k ≠ i → IsL2Ev ↥(Nb k) 1) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpi : ¬ p ∣ Nat.card ↥(Nb i)) : ¬ p ∣ Nat.card ↥(mbarImage D.M D.U (proofN D)) := by
  intro h
  obtain ⟨k, hk⟩ := uc22k_exists_index_bar D hNb hp h
  by_cases hki : k = i
  · subst hki
    exact hpi hk
  · rw [P22y.card_of_isL2Ev_one (hS3 k hki)] at hk
    rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 from hk) with h' | h' <;>
      have := Nat.le_of_dvd (by norm_num) h' <;> omega

theorem uc22p2251n_calCGS_le (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h33 : S22_3_3 D Ch) (hH : H1930 D) (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {i : Fin m} (hS3 : ∀ k, k ≠ i → IsL2Ev ↥(Nb k) 1)
    (hbad : IsL2Ev ↥(Nb i) 2 ∨ IsL3 ↥(Nb i) 1 ∨ IsS5 ↥(Nb i)) {p : ℕ} (hp : p ∈ D.sig) (hp5 : 5 ≤ p)
    (hpi : ¬ p ∣ Nat.card ↥(Nb i)) : UC6.calCGS (proofS D) ≤ D.M := by
  have hpp := (D.sig_prime p hp).1
  obtain ⟨P, hPM, hPp, hPbar, hnJ⟩ :=
    uc22k_exists_p_normalizing_jOf_bar D hpp (P2251n.not_dvd_card_of_not_dvd D hNb hS3 hpp hp5 hpi)
  have hPJ : P ≤ normalizer (jOf D.T : Set G) := fun y hy =>
    CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem (hnJ y hy)
  have hrk : 1 < CFSG.pRank p (MBar D.M D.U) :=
    uc22p22n_one_lt_pRank_mbar D hx h61 (uc22p22e_inCalV_U D) c.hU p hp
  have hnc : ¬ IsCyclic ↥(mbarImage D.M D.U P) := by
    refine uc22p22e_not_isCyclic_sylow hpp hPbar ?_
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    omega
  exact P2251g.calCGS_le D h61 hp hPM hPp hPJ
    (uc22p2251f_le_centralizer D Ch h33 hH c hNb hS3 hbad hpp hp5 hPM hPJ hPp) hnc

@[expose] def S22_5_1R3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)),
    NbarSplit D Nb → ∀ i, (D.k = 1 ∨ ∀ p ∈ D.sig, p ∣ Nat.card ↥(Nb i)) →
      ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
