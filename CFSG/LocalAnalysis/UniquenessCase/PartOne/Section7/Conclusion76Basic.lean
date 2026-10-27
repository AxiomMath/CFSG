module

public import CFSG.GroupTheory.CoprimeHyperplaneCentralizer
public import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
public import CFSG.LieType.BorelTits.Basic
import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem rankThreeGamma_le_of_forall_normalizer_le {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    {M E : Subgroup G}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M) (hE : CFSG.Open.IsElemAbelian r E)
    (hX : ∀ X : Subgroup G, X ≤ E → Nat.card X = r →
      1 < CFSG.Open.pRank p (M ⊓ Subgroup.normalizer (X : Set G)))
    (hN : ∀ X : Subgroup G, X ≤ E → Nat.card X = r →
      Subgroup.normalizer (X : Set G) ≤ M) :
    CFSG.Open.rankThreeGamma 1 r E ≤ M := by
  refine CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le (q := r) hM
    (CFSG.Open.IsElemAbelian.isPGroup hE) ?_
  intro X hXE hXcard
  exact ⟨hN X hXE hXcard, (CFSG.GroupTheory.dvd_card_of_one_le_pRank (Fact.out : p.Prime) (le_of_lt (hX X hXE hXcard))).trans
    (Subgroup.card_dvd_of_le inf_le_right)⟩

theorem rankThreeGamma_self_le {p : ℕ} [Fact p.Prime] {M E : Subgroup G}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M) (hEM : E ≤ M) (hE : IsPGroup p E) :
    CFSG.Open.rankThreeGamma 1 p E ≤ M := by
  refine CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le (q := p) hM hE ?_
  intro X hXE hXcard
  have hXp : IsPGroup p X := hE.to_le hXE
  have hXne : X ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hXcard
    have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
    omega
  refine ⟨hM.normalizer_le hXne hXp (hXE.trans hEM), ?_⟩
  rw [← hXcard]
  exact Subgroup.card_dvd_of_le Subgroup.le_normalizer

theorem rankThreeGamma_two_le {p : ℕ} [Fact p.Prime] {M E : Subgroup G}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (huniq : ∀ D : Subgroup G, D ≠ ⊥ → IsPGroup 2 D →
      2 ≤ CFSG.Open.pRank p (Subgroup.normalizer (D : Set G) ⊓ M) →
      Subgroup.normalizer (D : Set G) ≤ M)
    (hE : CFSG.Open.IsElemAbelian 2 E)
    (hX : ∀ X : Subgroup G, X ≤ E → Nat.card X = 2 →
      1 < CFSG.Open.pRank p (M ⊓ Subgroup.normalizer (X : Set G))) :
    CFSG.Open.rankThreeGamma 1 2 E ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine rankThreeGamma_le_of_forall_normalizer_le (p := p) (r := 2) hM hE hX ?_
  intro X hXE hXcard
  refine huniq X ?_ ?_ ?_
  · rintro rfl
    rw [Subgroup.card_bot] at hXcard
    omega
  · exact (CFSG.Open.IsElemAbelian.isPGroup hE).to_le hXE
  · rw [inf_comm]
    have h := hX X hXE hXcard
    omega

theorem exists_card_eq_not_le_centralizer_pCoreOf_inf_centralizer
    (hchar : CFSG.Open.IsCharTwoType G) {M : Subgroup G} (hM : CFSG.Open.IsTwoLocal M)
    {r : ℕ} [Fact r.Prime] (hr : r ≠ 2) {E : Subgroup G} (hEM : E ≤ M)
    (hE : CFSG.Open.IsElemAbelian r E) (hcard : Nat.card E = r ^ 2) :
    ∃ Y : Subgroup G, Y ≤ E ∧ Nat.card Y = r ∧
      ¬ E ≤ Subgroup.centralizer
        ((CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := CFSG.Open.pCoreOf 2 M
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M
  have hEQ : E ≤ Subgroup.normalizer (Q : Set G) :=
    hEM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hrQ : ¬ r ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    rintro hdvd
    rw [hn] at hdvd
    exact hr (Nat.prime_eq_prime_of_dvd_pow (Fact.out : r.Prime) Nat.prime_two hdvd)
  have hfaith : ¬ E ≤ Subgroup.centralizer (Q : Set G) := by
    intro hEcent
    have hEsubQ : E ≤ Q := (le_inf hEM hEcent).trans (hchar M hM)
    have hdisj : Disjoint E Q :=
      (IsPGroup.disjoint_of_ne 2 r (Ne.symm hr) Q E hQp
        (CFSG.Open.IsElemAbelian.isPGroup hE)).symm
    have hbot : E = ⊥ := by
      have hle : E ≤ E ⊓ Q := le_inf le_rfl hEsubQ
      rw [hdisj.eq_bot] at hle
      exact le_bot_iff.mp hle
    have h1 : Nat.card E = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hcard] at h1
    have h2 : 1 < r ^ 2 := by
      have := (Fact.out : r.Prime).two_le
      nlinarith
    omega
  obtain ⟨Y, hYE, hYcard, hYcent⟩ :=
    CFSG.GroupTheory.exists_hyperplane_not_le_centralizer_inf_centralizer (r := r) hE
      (by rw [hcard]) hEQ hrQ hfaith
  refine ⟨Y, hYE, ?_, hYcent⟩
  have h : Nat.card Y * r = r * r := by
    rw [hYcard, hcard, pow_two]
  exact Nat.eq_of_mul_eq_mul_right (Fact.out : r.Prime).pos h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
