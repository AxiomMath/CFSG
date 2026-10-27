module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem uc22p21m_hsig3_ofSetup (hS : Standing G) (S : Setup G) (hMS : S.InMSigma) :
    3 < CFSG.Open.pRank 3 S.M → 3 ∈ (PartTwo.Three.dataOfSetup hS S).sig := by
  classical
  intro h
  have hloc : CFSG.Open.pRank 3 S.M ≤ rankThreeLocalRank 3 G :=
    local_pRank_le_localRank 3 (by norm_num) S.M S.witness.maxLocal.1
  have hdvd : 3 ∣ Nat.card G := prime_dvd_card_of_pRank_pos 3 S.M (by omega)
  have hS1 : 3 ∈ {p : ℕ | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ 3 < rankThreeLocalRank p G} :=
    ⟨Nat.prime_three, by norm_num, hdvd, by omega⟩
  have h3A : 3 ∈ rankThreeSigmaA G := by
    unfold rankThreeSigmaA
    simp only
    rw [if_pos ⟨3, hS1⟩]
    exact hS1
  have hp3 : S.p = 3 := hMS.1 h3A
  obtain ⟨q, Q, hQ, rfl⟩ : ∃ (q : ℕ) (Q : Sylow q G), IsWitness q Q S.M ∧ q = 3 :=
    ⟨S.p, S.P, S.witness, hp3⟩
  exact ⟨h3A, Q, hQ⟩

theorem uc22p21m_hsig3_ofSetup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) :
    3 < CFSG.Open.pRank 3 S.M → 3 ∈ (UC6.dataOfSetup4 hS hU S).sig := by
  intro h
  have hloc : CFSG.Open.pRank 3 S.M ≤ rankThreeLocalRank 3 G :=
    local_pRank_le_localRank 3 (by norm_num) S.M S.maxLocal.1
  have hdvd : 3 ∣ Nat.card G := prime_dvd_card_of_pRank_pos 3 S.M (by omega)
  have h3B : 3 ∈ uniqueFourBeta G := ⟨Nat.prime_three, by norm_num, hdvd, by
    show 4 ≤ rankThreeLocalRank 3 G
    omega⟩
  have hp3 : S.p = 3 := hMS.1 h3B
  have := S.hp
  rw [hp3] at this
  exact this

end CFSG.LocalAnalysis.UniquenessCase.UC22
