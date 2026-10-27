module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineFive
import CFSG.LocalAnalysis.RankThreeUC.TheoremDReductions
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.ClauseBMap.ClauseBMap
import CFSG.LocalAnalysis.AGL81TheoremCD.AlmostStrongCoreMap

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsWitness.smul {p : ℕ} (hp : 1 < p) {P : Sylow p G} {M : Subgroup G}
    (hw : IsWitness p P M) (g : G) :
    IsWitness p (g • P) (M.map (MulAut.conj g).toMonoidHom) := by
  have hc := hw.isCoreWitness.map hp (MulAut.conj g)
  rw [← sylow_conjugate_eq_map] at hc
  refine ⟨hc.maxLocal, hc.u0, ?_, hc.u2⟩
  rw [sylow_conjugate_eq_map]
  rcases hw.u1 with h1 | h2 | ⟨h3, hC⟩
  · left
    rw [← gamma_map_automorphism 1 p hp]
    exact Subgroup.map_mono h1
  · right; left
    exact ProofSupport.ClauseBMap.clauseB_map (MulAut.conj g) h2
  · right; right
    exact ⟨h3, CFSG.LocalAnalysis.AGL81TheoremCD.rankThreeClauseC_map hC g⟩

end CFSG.LocalAnalysis.RankThreeUC

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem mem_sigmaOf_of_three_le_pRank (hS : Standing G) (hUC : rankThreeUC G) {M : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) {r : ℕ} (hr : r.Prime) (h7 : 7 ≤ r)
    (h3 : 3 ≤ CFSG.Open.pRank r M) : r ∈ sigmaOf M := by
  have hr2 : r ≠ 2 := by omega
  have hloc : rankThreeLocalRank r G = 3 := by
    have h1 := local_pRank_le_localRank r hr.one_lt M hM.1
    have h2 := rankThreeLocalRank_le_evenRank (G := G) r hr hr2
    rw [hS.rank] at h2
    omega
  have hdvd : r ∣ Nat.card G := prime_dvd_card_of_pRank_pos r M (by omega)
  have hrA : r ∈ rankThreeSigmaA G :=
    CFSG.LocalAnalysis.RankThreeUC.AGL81C.mem_sigmaA_of_large hS.rank hr (by omega) hdvd hloc
  obtain ⟨R, N, hw⟩ := rankThreeUC_iff.mp hUC r hrA
  obtain ⟨g, hg⟩ := hw.exists_le_conj_of_two_le_pRank hS hrA hM.1 (by omega)
  have hw' := hw.smul hr.one_lt g
  have hNM : N.map (MulAut.conj g).toMonoidHom = M := hM.2 _ hw'.maxLocal.1 hg
  exact ⟨hrA, g • R, hNM ▸ hw'⟩

theorem sigmaRankThree13_dataOfSetup (hS : Standing G) (hUC : rankThreeUC G) (S : Setup G) :
    SigmaRankThree13 (dataOfSetup hS S) :=
  fun _ _ hr h7 h3 => mem_sigmaOf_of_three_le_pRank hS hUC S.witness.maxLocal hr h7 h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
