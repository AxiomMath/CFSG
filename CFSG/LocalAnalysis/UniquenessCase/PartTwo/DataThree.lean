module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

@[expose] def sigmaOf (M : Subgroup G) : Set ℕ :=
  {q | q ∈ rankThreeSigmaA G ∧ ∃ Q : Sylow q G, IsWitness q Q M}

@[expose] def sigmaOneOf (M : Subgroup G) : Set ℕ :=
  {q | q ∈ rankThreeSigmaA G ∧ ∃ Q : Sylow q G, IsWitness q Q M ∧
    rankThreeGamma 1 q (Q : Subgroup G) ≤ M}

@[expose] def sigmaTwoOf (M : Subgroup G) : Set ℕ :=
  {q | q ∈ rankThreeSigmaA G ∧ ∃ Q : Sylow q G, IsWitness q Q M ∧
    rankThreeClauseB M (Q : Subgroup G) q}

@[expose] def sigmaThreeOf (M : Subgroup G) : Set ℕ :=
  {q | q = 3 ∧ q ∈ rankThreeSigmaA G ∧ ∃ Q : Sylow q G, IsWitness q Q M ∧
    rankThreeClauseC M (Q : Subgroup G)}

theorem prime_of_mem_rankThreeSigmaA {q : ℕ} (hq : q ∈ rankThreeSigmaA G) : q.Prime ∧ q ≠ 2 :=
  ⟨sigmaA_prime q hq, sigmaA_odd q hq⟩

theorem two_le_pRank_of_isWitness {q : ℕ} (hq : q ∈ rankThreeSigmaA G) {Q : Sylow q G}
    {M : Subgroup G} (hw : IsWitness q Q M) : 2 ≤ CFSG.Open.pRank q M := by
  classical
  have hprime : q.Prime := sigmaA_prime q hq
  have h3 : 3 ≤ rankThreeLocalRank q G := by
    have h := hq
    dsimp only [rankThreeSigmaA] at h
    split_ifs at h
    · exact le_of_lt h.2.2.2
    · exact h.2.2.2.ge
    · exact h.2.2.2.ge
    · exact h.2.2.2.ge
  obtain ⟨H, _, hHrank⟩ := rankThreeLocalRank_attained (G := G) q (by omega)
  obtain ⟨E, _, hEelem, hEcard⟩ := pRank_attained q H (by omega)
  obtain ⟨Q', hEQ'⟩ := (elementary_isPGroup q E hEelem).exists_le_sylow
  have hk : CFSG.Open.pRank q H ≤ CFSG.Open.pRank q (Q' : Subgroup G) := by
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove q hprime.one_lt (Q' : Subgroup G))
      ⟨E, hEQ', hEelem, hEcard⟩
  have hQ' : CFSG.Open.pRank q (Q' : Subgroup G) = CFSG.Open.pRank q (Q : Subgroup G) :=
    sylow_pRank_eq q hprime Q' Q
  have hQ2 : 2 ≤ CFSG.Open.pRank q (Q : Subgroup G) := by omega
  have hQM : (Q : Subgroup G) ≤ M :=
    le_normalizer.trans ((gamma_normalizer_le 2 q (Q : Subgroup G) (Q : Subgroup G) le_rfl
      hQ2).trans hw.u0)
  exact hQ2.trans (pRank_mono q hprime.one_lt hQM)

theorem sigmaOf_eq (M : Subgroup G) :
    sigmaOf M = sigmaOneOf M ∪ sigmaTwoOf M ∪ sigmaThreeOf M := by
  ext q
  simp only [sigmaOf, sigmaOneOf, sigmaTwoOf, sigmaThreeOf, Set.mem_setOf_eq, Set.mem_union]
  constructor
  · rintro ⟨hq, Q, hw⟩
    rcases hw.u1 with h1 | h2 | h3
    · exact Or.inl (Or.inl ⟨hq, Q, hw, h1⟩)
    · exact Or.inl (Or.inr ⟨hq, Q, hw, h2⟩)
    · exact Or.inr ⟨h3.1, hq, Q, hw, h3.2⟩
  · rintro ((⟨hq, Q, hw, _⟩ | ⟨hq, Q, hw, _⟩) | ⟨_, hq, Q, hw, _⟩)
    · exact ⟨hq, Q, hw⟩
    · exact ⟨hq, Q, hw⟩
    · exact ⟨hq, Q, hw⟩

@[expose] noncomputable def dataOfSetup (hS : Standing G) (S : Setup G) : Data G where
  M := S.M
  T := S.T
  sig := sigmaOf S.M
  sig1 := sigmaOneOf S.M
  sig2 := sigmaTwoOf S.M
  sig3 := sigmaThreeOf S.M
  standing := ⟨hS.simple, hS.nonab, hS.kProper, hS.charTwo, le_of_eq hS.rank.symm⟩
  maxLocal := S.witness.maxLocal
  sylowM := S.sylowM
  sylowG := S.sylowG
  normalizer_le := S.normalizer_le
  sig_prime := fun _ hq => prime_of_mem_rankThreeSigmaA hq.1
  sig_rank := fun _ hq => two_le_pRank_of_isWitness hq.1 hq.2.choose_spec
  sig_sub := sigmaOf_eq S.M

theorem mem_sigmaOf (S : Setup G) : S.p ∈ sigmaOf S.M := ⟨S.hp, S.P, S.witness⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
