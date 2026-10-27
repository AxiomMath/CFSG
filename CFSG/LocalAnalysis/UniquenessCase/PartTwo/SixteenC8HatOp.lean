module

import CFSG.Adapters.GeneralizedFitting
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.ReducedCentralizerObstruction
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem c8h_map_layer_eq {G : Type} [Group G] (I : Subgroup G) :
    (genFittingLayer ↥I).map I.subtype = rankThreeLayer I := by
  rw [CFSG.Adapters.genFittingLayer_eq_foundations,
    CFSG.LocalAnalysis.ComponentInitial.layer_map_subtype, rankThreeLayer]
  simp_rw [CFSG.Assembly.isComponentOf_iff_open]

theorem c8h_exists_op {Γ : Type} [Group Γ] [Finite Γ] {d : Γ} (h2 : CFSG.pCore 2 Γ = ⊥)
    (hF : ¬ Fstar (CFSG.pPrimeCore 3 Γ) ≤ centralizer ({d} : Set Γ))
    (hE : rankThreeLayer (CFSG.pPrimeCore 3 Γ) ≤ centralizer ({d} : Set Γ)) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ¬ CFSG.pCore p Γ ≤ centralizer ({d} : Set Γ) := by
  by_contra hcon
  have hcon' : ∀ p : ℕ, p.Prime → 3 < p →
      CFSG.pCore p Γ ≤ centralizer ({d} : Set Γ) := by
    intro p hp h3p
    by_contra h
    exact hcon ⟨p, hp, h3p, h⟩
  set I := CFSG.pPrimeCore 3 Γ
  have hIn : I.Normal := CFSG.pPrimeCore_normal
  have h3 : Nat.Coprime 3 (Nat.card ↥I) := CFSG.pPrimeCore_coprime_card
  have key : ∀ q ∈ (Nat.card ↥I).primeFactors,
      (CFSG.pCore q ↥I).map I.subtype ≤ centralizer ({d} : Set Γ) := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqI : q ∣ Nat.card ↥I := Nat.dvd_of_mem_primeFactors hq
    have hqne3 : q ≠ 3 := by
      intro hq3
      have h31 : (3 : ℕ) = 1 := Nat.Coprime.eq_one_of_dvd h3 (hq3 ▸ hqI)
      omega
    have hle : (CFSG.pCore q ↥I).map I.subtype ≤ CFSG.pCore q Γ :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_subgroup_pCore_le q I hIn
    rcases eq_or_ne q 2 with hq2 | hq2
    · have hq2le : CFSG.pCore q Γ ≤ centralizer ({d} : Set Γ) := by
        rw [hq2, h2]
        exact bot_le
      exact hle.trans hq2le
    · have h3q : 3 < q := by
        have := hqprime.two_le
        omega
      exact hle.trans (hcon' q hqprime h3q)
  have hFit : (genFittingFitting ↥I).map I.subtype ≤ centralizer ({d} : Set Γ) := by
    rw [CFSG.Adapters.genFittingFitting_eq_foundations, CFSG.fitting_eq_sup_pCore ↥I,
      Subgroup.map_iSup]
    exact iSup_le fun p => key p.1.1 p.1.2
  apply hF
  unfold Fstar
  rw [CFSG.Open.genFittingFStar.eq_sup, Subgroup.map_sup, c8h_map_layer_eq]
  exact sup_le hFit hE

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
